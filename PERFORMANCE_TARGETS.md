# Build performance: measured targets

Measured 2026-09-05 on a quiet machine, Isabelle2025-2, from the clean build at
commit `1e13e83` (`isabelle build -c`, `threads=4`).

- **Wall clock 1:20, CPU 3:25 (205 s).**
- Isabelle persistently stores the timing of every command above
  `build_timing_threshold` (0.1 s) in the session database. That is **424 commands
  totalling 187.2 s**, i.e. essentially all of the CPU cost.

Re-measure at any time with `tools/profile_timings.py`, which reads the timings
straight out of `Sigmoid_Universal_Approximation.db`, decompresses them, maps each
Isabelle symbol offset back to a line number, and attributes it to the enclosing
declaration. No instrumented rebuild is needed — an ordinary build refreshes the data.

## Where the time goes

| kind | calls | total | share |
|---|---:|---:|---:|
| `ML` (the audit block) | 1 | 52.3 s | 28 % |
| `simp` | 101 | 34.4 s | 18 % |
| `auto` | 90 | 22.7 s | 12 % |
| `smt` | 57 | 18.9 s | 10 % |
| theory imports | 22 | 14.4 s | 8 % |
| `linarith` | 44 | 11.9 s | 6 % |
| statement elaboration (`have`/`lemma`/`show`) | 54 | 14.5 s | 8 % |
| `fastforce` | 15 | 6.1 s | 3 % |
| `metis`, `blast`, `force`, `argo`, `presburger` | 30 | 8.7 s | 5 % |
| `value` (leftover) | 1 | 1.0 s | 0.5 % |

Two items alone are **45 % of the build**.

## Tier 1 — the two dominant costs

### T1.1 `Proof_Audit.thy:6`, the ML audit block — **52.3 s (28 %)**

Not a proof. It walks every stored fact of the session calling
`Thm_Deps.all_oracles`, which traverses proof terms transitively, then checks hidden
hypotheses, free term variables and non-definitional axioms.

The check is worth keeping — it is what makes the theorem statements trustworthy — but
every ordinary build pays for it, and its cost grows with the development.

*Attack (creative, not sledgehammer):* move `Proof_Audit` into its own session with
`Sigmoid_Universal_Approximation` as parent. Day-to-day builds then cost 52 s less, and
the audit runs as a separate target in CI and before releases. `ROOT` gains one session
stanza; no proof changes. Alternative if it must stay inline: restrict `all_oracles` to
the theorems actually exported rather than all 500-odd stored facts.
**Expected saving: ~52 s off the default build.** Risk: low, but the audit must not
become something nobody runs — it needs to stay wired into the release path.

### T1.2 `Universal_Approximation_1d.thy:59`, `sigmoidal_approximation_fixed_parameters` — **32.4 s (17 %)**

A single lemma spanning **lines 59–1341, 1,283 lines**. Its slowest interior commands:

| line | cost | tactic |
|---|---:|---|
| 755 | 1.29 s | `using f_diff_lt_eta mult_strict_mono sigma_lt_inverseN by fastforce` |
| 1043 | 1.25 s | *byte-identical to line 755* |
| 641 | 1.26 s | `by (smt (verit, best) f1 f2 sum_mono)` |
| 224 | 1.25 s | `by (smt (verit) GreatestI_nat atLeastAtMost_iff j_def)` |
| 564 | 1.09 s | `by (simp add: sum_subtractf)` |
| 625 | 0.97 s | `by linarith` |
| 551 | 0.95 s | `by (smt (verit, ccfv_SIG) G_Nf_def sum_mono sum_of_terms)` |

*Attack (creative):* split it into named sub-lemmas. Three separate wins: Isabelle forks
proofs in parallel, and a 1,283-line monolith is **one** task on **one** core, so the
split buys parallelism the current shape cannot use; the duplicated `fastforce` at 755
and 1043 becomes one shared lemma (~1.25 s); and each remaining slow step becomes
individually visible and attackable. **Expected saving: 1.3 s from the duplicate
directly, plus a large wall-clock win from parallelism on a 12-core machine.**
Risk: medium — it is the core of Theorem 2.1, so the split must be statement-preserving,
checked the way the `Paper_` dissolution was.

## Tier 2 — the `smt` cluster: 18.9 s over 57 calls

63 `smt` calls remain, concentrated in `Universal_Approximation_1d.thy` (32),
`Asymptotic_Qualitative_Properties.thy` (8), `Sigmoid_Definition.thy` (6),
`Simultaneous_Approximation.thy` (6), `Partition_Facts.thy` (4),
`Derivative_Identities_Smoothness.thy` (4), `Simultaneous_Approximation_General_j.thy` (2),
`Concrete_Sigmoidal_Examples.thy` (1).

They are oracle-free — `Proof_Audit` would reject them otherwise — but each one re-runs
an external solver and reconstructs a proof on every build.

Hottest, in order: `Universal_Approximation_1d.thy:641` (1.26 s), `:224` (1.25 s),
`:551` (0.95 s), `Partition_Facts.thy:135` (0.94 s),
`Asymptotic_Qualitative_Properties.thy:351` (0.91 s),
`Simultaneous_Approximation.thy:117` (0.81 s).

Note `Universal_Approximation_1d.thy:224` and `Partition_Facts.thy:135` are the **same
proof** — `by (smt (verit) GreatestI_nat atLeastAtMost_iff j_def)`, 2.19 s combined.

*Attack:* this is where sledgehammer earns its place — ask it for a `metis`/`simp`
one-liner and keep the reconstruction rather than the `smt` call. Today's evidence says
the elementary replacement is also the fast one: `neg_wh_le_Nbot` went from an
`smt (verit, ccfv_SIG)` call to four `linarith`/`simp only` steps.
**Expected saving: most of 18.9 s.** Risk: low, one call at a time.

## Tier 3 — individually pathological `simp`/`auto` sites

| location | cost | command |
|---|---:|---|
| `Simultaneous_Approximation.thy:1061` | 2.52 s | a bare `by simp` |
| `Simultaneous_Approximation_Rate.thy:81` | 2.07 s | a bare `by simp` — *same text* |
| `Multivariate_Approximation.thy:2049` | 2.14 s | `by (intro add_mono) auto` |
| `Simultaneous_Approximation.thy:2024` | 1.09 s | `by linarith` after `abs_triangle_ineq` |
| `Simultaneous_Approximation.thy:1217` | 0.85 s | `by (simp add: sum_subtractf right_diff_distrib' left_diff_distrib')` |

A bare `simp` costing 2.5 s is doing far more search than the goal needs — both sites
follow `unfolding C1_def M1_def` with a large `using`, so simp is re-deriving arithmetic
that could be handed to it. *Attack:* `simp only:` with the needed rules, or split the
arithmetic out the way the `example_g_cubic_ineq` step was.
**Expected saving: 5–7 s.** Risk: low.

## Tier 4 — duplicated proof work

`forward_diff_one_J1_eta_bound` (`Simultaneous_Approximation.thy:1014`, 3.67 s) and
`forward_diff_one_J1_rate_bound` (`Simultaneous_Approximation_Rate.thy:46`, 3.27 s) are
the same proof with two different conclusions — an η-form and a rate-form — differing
only in three hypotheses and the final bound. **6.9 s, largely duplicated.**

*Attack (creative):* prove the shared estimate once and derive both conclusions from it.
**Expected saving: ~3 s**, and one fewer place to keep in sync. Risk: medium, it needs
the common generalisation stated correctly.

## Tier 5 — free

`Universal_Approximation_1d.thy:44`: `value "unif_part (0::real) 1 4"`, a debugging
leftover with the expected output in a comment beside it. **1.0 s every build**, no
contribution to the development. Delete it, or keep the comment and drop the `value`.
Risk: none.

## Not worth attacking

- **Theory imports, 14.4 s.** The largest is `Sigmoid_Definition` at 5.0 s, which pulls
  in `HOL-Combinatorics.Stirling`. That is genuinely used — `nth_derivative_sigmoid`
  expresses the n-th derivative of the sigmoid through Stirling numbers of the second
  kind — so the import is earned.
- **`nth_derivative_sigmoid`, 4.8 s.** A real induction over a Stirling-number identity.
  Expensive because the mathematics is, not because the proof is sloppy.

## Order of attack

1. **T5** — delete the `value`. Seconds of work.
2. **T1.1** — split `Proof_Audit` into its own session. Biggest single win, no proof risk.
3. **T2** — the `smt` cluster, hottest first, one at a time.
4. **T3** — the pathological `simp` sites.
5. **T1.2** — split the 1,283-line monolith. Largest structural payoff, do it when the
   cheaper wins are banked so its effect is measurable in isolation.
6. **T4** — merge the duplicated forward-difference bound.

Re-run `tools/profile_timings.py` after each step; the numbers above are the baseline.
