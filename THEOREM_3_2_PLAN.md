# Historical plan: Theorems 3.2, 5.4 and 5.2

This is a historical development log, not the current completion statement.
See [PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) and
[PAPER_FIXES_TODO.md](PAPER_FIXES_TODO.md) for the 2026-09-05 source-verified repairs,
the counterexample to the printed Theorem 5.2 bound, the subsequent explicit general-Lp
mollifier construction, the translated-domain Lp follow-up, and the later structural repair
that deleted the two unused mollifier developments and renamed the surviving theories
(`Lp_Mollifiers.thy` -> `Lp_Density.thy`; the paper construction -> `Mollifiers.thy`,
`Mollifier_Networks.thy`, `Translated_Lp_Approximation.thy`). Theory and constant names below
are the historical ones. Earlier "DONE" descriptions below concern
the then-existing density-based statements, not complete reproduction of the paper.

## `Lp_norm_eq_seminorm` DEFECT: DIAGNOSED AND FIXED (2026-09-03)

Root cause found by minimal reproduction, not guessed. Stated as a bare
`lemma Lp_norm_eq_seminorm: "Lp_norm p a b h = Lp_seminorm p (lebesgue_on {a..b}) h"`, the
theorem was stored as
`Lp_norm ?p ?a ?b h = Lp_seminorm ?p (lebesgue_on {?a..?b}) h`
-- `?p`, `?a`, `?b` schematic but **`h` a FIXED free variable, not generalized**. So `rule`/`simp`
could only ever apply it to a function literally named `h`, and it failed at every call site
while the goal still printed as exactly its own instance. Renaming to `hh` generalized fine
(`?hh`), confirming the name `h` specifically is bound in this theory's ambient context.
**Fix: give the lemma an explicit `fixes p a b :: real and h :: "real \<Rightarrow> real"` clause.** Both
Theorem 3.2 call sites now cite it directly instead of inlining
`unfolding Lp_norm_def Lp_seminorm_def`. Capstone rebuilt green.
**Same root cause as the earlier "No such variable in theorem: ?h" on `abs_powr_measurable`** --
that was cured by adding `fixes h` too, which is why it worked. GENERAL RULE for this project:
**always give a `fixes` clause; never rely on a bare `lemma` generalizing its free variables**,
because at least the name `h` does not generalize here.

## THEOREM 5.2 -- SCOPED, NOT STARTED (2026-09-03). This is a LARGE piece of work.

Paper statement (p.185, proof p.185-186): for `\<sigma>` bounded sigmoidal and `f \<in> C(Q)`
H\<ouml>lder-continuous of order `\<alpha>`, `0<\<alpha>\<le>1`, with constant `L>0`: for every `N>2` there is `w\<^bsub>0\<^esub>>0`
such that for `w \<ge> w\<^bsub>0\<^esub>`,
`\<parallel>G\<^sub>N f - f\<parallel>\<^sub>\<infinity> < (1/N powr \<alpha>) * [L*2 powr (\<alpha>/2+1)*(b-a) powr \<alpha> + 2 powr (\<alpha>/2)*(b-a) powr \<alpha>*\<parallel>\<sigma>\<parallel>\<^sub>\<infinity> + \<parallel>f\<parallel>\<^sub>\<infinity>]`.

Unlike 3.2/5.4 this is NOT a density/Minkowski argument -- it is a QUANTITATIVE RATE, obtained by
redoing Theorem 5.1's `H\<^sub>1`/`H\<^sub>2` estimate with explicit constants (the paper: "by simple
modifications in the proof of Theorem 5.1"). Two things make it expensive here:

1. **The existing `multivariate_network_H1_bound` is NOT reusable as-is.** It bounds
   `\<bar>network - local_proxy\<bar>` by `card(column_index)*M*\<epsilon>*(2N+1) + M*\<epsilon>*(2N-1)`, i.e. it has
   already thrown away the `f`-differences by bounding `\<bar>\<Delta>f\<bar> \<le> 2M`. Theorem 5.2 needs the FINER
   intermediate form that keeps `(1/N\<^sup>2)\<Sum>\<Sum>\<bar>f(x\<^sub>i,y\<^sub>j) - f(x\<^sub>i,y\<^sub>j\<^sub>-\<^sub>1)\<bar>`, so that each difference can then be
   bounded by `L*(\<surd>n h) powr \<alpha>`. That means refined variants of BOTH
   `multivariate_network_other_columns_bound` and `multivariate_network_same_column_bound`
   (each already large), plus a refined `H\<^sub>2`.
2. **The n-d generalization changes the paper's constants.** The paper's `2 powr (\<alpha>/2)` comes from
   `\<parallel>(x,y)-(x\<^sub>k,y\<^sub>\<mu>\<^sub>-\<^sub>1)\<parallel> \<le> \<surd>2 h` in its 2-d setting; in `CARD('n)` dimensions this becomes
   `\<surd>(CARD('n)) h`, i.e. `CARD('n) powr (\<alpha>/2)`. The user wants n-d throughout Section 5, so the
   theorem statement must be re-derived with the right constant -- not transcribed.

Also needed: an n-d H\<ouml>lder-continuity predicate (the project has only `deriv_lipschitz_bound`,
`Derivative_Approximation.thy`, which is 1-d and about `f'`).

Estimated size: comparable to Theorem 5.1's own proof (a major effort per the project memory),
NOT the one-round assembly that 3.2 and 5.4 turned out to be.

### 5.2 PROGRESS (2026-09-04)

- [x] **`multivariate_network_other_columns_bound` REFINED and verified.** It now takes
      `Df :: real` with `Df_nonneg: "0 \<le> Df"` and
      `df_bound: "\<And>k' j'. k' \<in> column_index r0 N \<Longrightarrow> j' \<in> {1..N} \<Longrightarrow>
        \<bar>f (grid_point r0 xs k' j') - f (grid_point r0 xs k' (j' - 1))\<bar> \<le> Df"`,
      and concludes
      `\<le> card(column_index r0 N) * (real N * (Df * \<epsilon>)) + card(column_index r0 N) * (M * \<epsilon>)`
      instead of the old `card * M * \<epsilon> * (2*real N + 1)`. The old form is recovered at the
      `multivariate_network_H1_bound` call site by passing `Df := 2*M` (justified there by
      `grid_point_in_box` + `f_bound`) and `simp add: algebra_simps`. Theorem 5.1 unaffected;
      whole capstone session rebuilt GREEN.
      Why this was necessary: 5.1 picks `\<epsilon>'` AFTER `N` (as `\<epsilon>/(2(M+1)(D+1))`), so bounding
      `\<bar>\<Delta>f\<bar> \<le> 2M` costs nothing; 5.2 fixes `\<epsilon>' = 1/N\<^sup>2` FIRST, and then the crude bound gives
      `M*D/N\<^sup>2 ~ M*N^(n-2)`, which does not vanish. The per-term `f`-differences must survive.
- [x] `multivariate_H2_bound` needs NO refinement -- it is already parameterised by an abstract
      modulus (`f_cont: norm(p-q)<\<delta> \<Longrightarrow> \<bar>f p - f q\<bar> < \<eta>`, `h_lt: h*(CARD('n)+2)/2 < \<delta>`,
      conclusion `< (1+S)*\<eta>`). For 5.2 instantiate `\<eta> := L * \<delta> powr \<alpha>` with `\<delta>` any value
      just above `h*(CARD('n)+2)/2`.
- [x] `multivariate_network_same_column_bound` refined (same `Df` parameter; conclusion
      `\<le> (real N - 1) * (Df * \<epsilon>) + M * \<epsilon>`). NB its `df_bound` is indexed by `j'` only
      (the column `k` is fixed), so `H1_bound` passes `df_bound[OF k_range]`.
- [x] `multivariate_network_H1_bound` now carries `Df`; conclusion
      `\<le> (card * (real N * (Df*\<epsilon>)) + card * (M*\<epsilon>)) + ((real N - 1) * (Df*\<epsilon>) + M*\<epsilon>)`.
      Theorem 5.1 recovers its old numeric bound by passing `Df := 2*M` + `algebra_simps`.
- [x] `grid_point_adjacent_dist` (in `Multivariate_Holder_Rate.thy`):
      `norm (grid_point r0 xs k j - grid_point r0 xs k (j-1)) \<le> h` for `j \<in> {1..N}`, by
      `grid_point_r0_step_boundary` (`j=1`, gives `h/2`) and `grid_point_r0_step` (`j\<ge>2`, gives `h`).
      No new Hoelder predicate was introduced -- the condition is taken inline as a hypothesis
      `\<bar>f p - f q\<bar> \<le> L * norm (p - q) powr \<alpha>`, matching the project's preference for not adding
      definitions that occur once.
- [x] **THEOREM 5.2 PROVED AND VERIFIED**, `multivariate_holder_rate` in
      `Multivariate_Holder_Rate.thy`; added to the capstone, whole session builds GREEN.
      `\<lbrakk>sigmoidal \<sigma>; bounded_function \<sigma>; a<b; 0<N; 0<L; 0<\<alpha>; \<alpha>\<le>1;
        continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f;
        \<And>p q. \<dots> \<Longrightarrow> \<bar>f p - f q\<bar> \<le> L * norm (p - q) powr \<alpha>\<rbrakk> \<Longrightarrow>
       \<exists>w0>0. \<forall>w\<ge>w0. \<forall>z. (\<forall>r. z $ r \<in> {a..b}) \<longrightarrow>
         \<bar>multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z\<bar>
           < (1 + (1 + (SUP t. \<bar>\<sigma> t\<bar>)) * L * ((b-a)*(real CARD('n)+2)) powr \<alpha>) / real N powr \<alpha>`
      Structure: `Df := L * h powr \<alpha>` feeds the refined `H\<^sub>1`; `\<delta> := h*(CARD('n)+2)` and
      `\<eta> := L * \<delta> powr \<alpha>` feed the UNCHANGED `multivariate_H2_bound`; the saturation tolerance
      `\<epsilon>' := 1/(N powr \<alpha> * (B+1))` (with `B` collecting `H\<^sub>1`'s `N`- and column-count factors)
      makes `H\<^sub>1 < N powr -\<alpha>`; triangle inequality combines them.

### Gotchas hit while proving 5.2 (all cost one round each)

- `proof (intro exI[\<dots>] conjI \<dots> allI impI)` on `\<exists>w0>0. \<forall>w\<ge>w0. \<forall>z. P` strips BOTH the
  `\<forall>w` AND the inner `\<forall>z`; an inner `show "\<forall>z. \<dots>"` then "fails to refine any pending goal".
  Fix: `fix w :: real and z :: "(real,'n) vec"` and assume both in one go.
- `B / (real N powr \<alpha> * (B+1)) < 1 / real N powr \<alpha>` is NOT closed by `field_simps`. Factor it
  as `(B/(B+1)) * (1/N powr \<alpha>)` and use `mult_strict_right_mono` with
  `B/(B+1) < 1` by `divide_less_eq`.
- `1/D + C/D = (1+C)/D` is NOT closed by `field_simps` either; use `add_divide_distrib`.
- When renaming a bound in a large proof by textual substitution, the `coeff_bound` STATEMENTS
  and their PROOFS must both change -- `\<le> Df` proved by `f_bound[OF box1] f_bound[OF box2]`
  silently still derives `\<le> 2*M`. And when editing several sites by line number, process
  them in DESCENDING line order or insertions shift the later ones.

**NB the constant will NOT match the paper's.** The paper's `2 powr (\<alpha>/2)` comes from `\<surd>2 h` in
its 2-d setting; this project's `H\<^sub>2` machinery uses the mesh condition `h*(CARD('n)+2)/2 < \<delta>`,
so the n-d constant here is driven by `(CARD('n)+2)/2`, not `\<surd>(CARD('n))`. State the theorem with
this project's own constants and note the divergence -- do not transcribe the paper's.

**LaTeX trap (cost one failed build):** do NOT write `H\<ouml>lder` in a `.thy` comment -- the
session's document setup has no binding for `\<ouml>` and `document = pdf` then fails with
"Undefined control sequence" while all proofs succeed. Write `Hoelder`. Existing files use
`Holder` (e.g. `Lp_Holder_inequality`).

## NEXT TARGET: Theorem 5.4 (multivariate \<open>L\<^sup>p\<close>, \<open>f\<close> not continuous) -- scoped 2026-09-03

Checked against the actual files (the project memory was STALE on this and has been corrected):
`Multivariate_Approximation.thy` already contains **Theorem 5.1**
(`multivariate_uniform_approximation`) and **Theorem 5.3**
(`multivariate_sigmoidal_Lp_approximation_theorem`), the latter assuming
`contin_f: "continuous_on {z. \<forall>r. z $ r \<in> {a..b}} f"` and concluding
`\<exists>N. \<exists>w>0. N>0 \<and> multivariate_Lp_norm p a b (\<lambda>z. multivariate_network \<sigma> f r0 (unif_part a b N) N w z - f z) < \<epsilon>`,
with `multivariate_Lp_norm p a b g = (\<integral>z. \<bar>g z\<bar> powr p \<partial>(lebesgue_on {z. \<forall>r. z $ r \<in> {a..b}})) powr (1/p)`.

So **Theorem 5.4 is Theorem 3.2's argument verbatim, one dimension up**: zero-extend `f` off the
box, get a continuous `g` nearby in `L\<^sup>p`, apply Thm 5.3 to `g`, combine with Minkowski. The ONLY
missing ingredient is `continuous_dense_Lp` at `(real,'n::finite) vec` instead of `real`.

**The generalization is mechanical -- PROVED by probe, not assumed.** `outer_regular_lborel` is
already generic over `'a::euclidean_space`; the only `real`-specific step in the whole density
chain is `inner_regular_lborel`'s use of `{- real n .. real n}`. Generalizing it needs exactly
four edits, verified clean in a scratch theory on the first try:
  `{- real n .. real n}` \<rightarrow> `cball 0 (real n)`; `compact_Icc` \<rightarrow> `compact_cball`;
  `\<bar>x\<bar> \<le> real n` \<rightarrow> `norm x \<le> real n`; and `by auto`/`by simp` \<rightarrow>
  `by (simp add: mem_cball dist_norm)` / `by (auto simp: mem_cball)` at the two `cball`
  membership steps.
**STATUS: the generalization is DONE and verified (2026-09-03).** `Lp_Mollifiers.thy`'s whole
density chain is now stated over `'a::euclidean_space`:
`inner_regular_lborel`, `tent` (now `'a set \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real`) + `tent_near`/
`tent_eq_zero_off`/`tent_eq_zero_far`, `indicator_continuous_approx`, `abs_powr_measurable`,
`simple_dense_Lp`, `simple_Lp_level_finite`, `indicator_scaled_Lp_approx`,
`simple_continuous_approx`, `continuous_dense_Lp`. The 1-d mollifier material was left alone.
Regression check: the full capstone session still builds green (Theorem 3.2 uses the generalized
chain at `'a := real`). Edits actually needed, beyond the four in `inner_regular_lborel`:
`tent_eq_zero_far`'s `\<bar>y\<bar>`/`\<bar>x\<bar>` \<rightarrow> `norm y`/`norm x` (with `abs_triangle_ineq` \<rightarrow>
`norm_triangle_ineq`, `dist_real_def` \<rightarrow> `dist_norm`), the matching `norm` in
`indicator_continuous_approx`'s `\<exists>R. \<forall>x. R < norm x \<longrightarrow> g x = 0` conclusion and its `R0`
`obtain` (drop `real_norm_def` from the simp set), the `fix g :: "'a \<Rightarrow> real" and x :: 'a`
annotations inside the `key`/`wrap` blocks, the `\<lambda>_::'a. 0::real` witnesses in the two
empty-case branches, and `define f0 :: "'a \<Rightarrow> real"` in `simple_dense_Lp`. NB the inner
`\<lambda>t::real. \<bar>t\<bar> powr p` in `abs_powr_measurable` stays `real` -- it is the outer function, not
the domain.
**THEOREM 5.4 IS PROVED AND VERIFIED (2026-09-03), first attempt, no corrections.**
`Multivariate_Lp_Approximation_General.thy` (imports `Multivariate_Approximation` +
`Lp_Approximation_General`), theorem
`multivariate_sigmoidal_Lp_approximation_theorem_general`:
`\<lbrakk>sigmoidal \<sigma>; bounded_function \<sigma>; continuous_on UNIV \<sigma>; a<b; f \<in> borel_measurable borel;
  integrable (lebesgue_on {z. \<forall>r. z $ r \<in> {a..b}}) (\<lambda>z. \<bar>f z\<bar> powr p); 1\<le>p; 0<\<epsilon>\<rbrakk> \<Longrightarrow>
 \<exists>g. continuous_on {z. \<forall>r. z $ r \<in> {a..b}} g \<and> (\<exists>N w. 0<w \<and> 0<N \<and>
   multivariate_Lp_norm p a b
     (\<lambda>z. multivariate_network \<sigma> g r0 (unif_part a b N) N w z - f z) < \<epsilon>)`
Added to the capstone imports; full session build GREEN (exit 0, ~29 s, PDF included).

**KEY STRUCTURAL DIFFERENCE from Theorem 3.2, do not miss it:** `multivariate_network` is NOT
continuous in `z`, so integrability of `\<bar>G\<^sub>N g - g\<bar>\<^sup>p` cannot come from continuity on a compact
set the way it did in 1-d; and a small `Lp_seminorm` does NOT imply integrability, so
`Lp_Minkowski_inequality` genuinely needs it as a side condition. Consequence: **Theorem 5.3
cannot be used as a black box here** (it yields only the norm bound). Instead mirror 5.3's own
proof -- apply `multivariate_uniform_approximation` to the continuous approximant `g`, then read
integrability off the uniform bound with `finite_measure.integrable_const_bound`, which gives the
`L\<^sup>p` estimate and the integrability together. Budget: `\<epsilon>/4` for density + `\<epsilon>/4` for the network.

To make this work the measure bridges in `Lp_Approximation_General.thy` were generalized from
`{a..b}` to an arbitrary `S \<in> sets borel` over `'a::euclidean_space`
(`powr_indicator_measurable`, `powr_indicator_integrable`, `integrable_powr_restrict_gen`,
`Lp_seminorm_restrict_le`, `integrable_powr_zero_extension_gen`), with the old `{a..b}` names
kept as thin corollaries so Theorem 3.2's call sites were untouched.
Scratch heaps now: `Lp_Moll_Deps`, `Thm32_Deps`, `Thm54_Deps` (ROOTs under the session
scratchpad in `deps/`, `deps2/`, `deps3/`). Delete when done.

Original plan (superseded by the STATUS note above): generalise IN PLACE in `Lp_Mollifiers.thy` from `real` to `'a::euclidean_space`
(`inner_regular_lborel`, `tent` + its six lemmas, `indicator_continuous_approx`,
`abs_powr_measurable`, `simple_dense_Lp`, `indicator_scaled_Lp_approx`,
`simple_continuous_approx`, `continuous_dense_Lp`); `Lp_seminorm_sum`/`Lp_seminorm_scale`/
`measure_lt_of_emeasure_lt` are already generic. The 1-d mollifier material in the same file
(`H_integral_1d`, `mollifier_1d`, `convolution_1d`, ...) is NOT part of this chain -- leave it
alone. Theorem 3.2 keeps working unchanged, since `real` is a `euclidean_space`.
Then Theorem 5.4 goes in a new theory beside `Lp_Approximation_General.thy`.

---

# Plan: assemble Theorem 3.2 (Costarelli-Spigler)

Goal: prove `sigmoidal_Lp_approximation_theorem_general` (or similar name) in
`Lp_Approximation.thy`: for `\<sigma>` bounded sigmoidal, `f \<in> L^p[a,b]` (via `Lp_norm`, NOT assumed
continuous or bounded), `1 \<le> p < \<infinity>`, `\<epsilon> > 0`, there exist `N`, `w>0` with
`Lp_norm p a b (\<lambda>x. G_N f x - f x) < \<epsilon>`. Paper proof: p.173-174 of
`/home/dusty/Desktop/Costarelli-Spigler-ATA-2013-2.pdf` (also copied to
`/home/dusty/Desktop/Academic/Isabelle_Stuff/Costarelli-Spigler-ATA-2013-2.pdf`).

**Read `/home/dusty/.claude/projects/-home-dusty-Desktop/memory/sigmoid-universal-approximation-formalization.md`
and `/home/dusty/.claude/projects/-home-dusty-Desktop/memory/mollifier-theory-scoping.md` first** --
they have the full narrative of how we got here, including two "we thought this was just
assembly and it wasn't" corrections. This was the authoritative TODO at that historical stage;
the current source-verified checklist is now `PAPER_FIXES_TODO.md`. The unchecked pieces below
are preserved as historical route choices, not additional current implementation gaps.

## Progress checklist (update this as you go -- this is how a fresh loop tick knows where to resume)

- [x] `Lp_Inequalities.thy` -- `Lp_seminorm`, `Lp_Holder_inequality`, `Lp_Minkowski_inequality`. DONE, verified, wired into `Sigmoid_Universal_Approximation.thy`.
- [x] `Mollifiers.thy` -- full `(real,'n::finite) vec` mollifier theory (not directly reused here except two generic lemmas). DONE.
- [x] `Lp_Mollifiers.thy` piece 1+2 -- `H_integral_1d`, `mollifier_1d`, `mollifier_1d_integral_one`, `convolution_1d`. DONE, verified.
- [x] Piece 3: `mollifier_1d_continuous` (`continuous_on UNIV (mollifier_1d k)`), `mollifier_1d_measurable` (`mollifier_1d k \<in> borel_measurable borel`), `mollifier_1d_bound` (`mollifier_1d k x \<le> real k / H_integral_1d`). DONE, verified. NB: `H_continuous_on_1d`'s set is schematic -- cite it as `H_continuous_on_1d[of UNIV]` or `continuous_on_compose2` unifies it into a nonsense `closed_segment` side goal.
- [ ] Piece 4: continuity of `convolution_1d k \<star>\<^sub>1 f`. **REVISED (better than the Hölder route below)**: assume `integrable lborel f` (i.e. `f\<in>L^1`) instead of `f\<in>L^p`, and dominate globally by `C*\<bar>f y\<bar>` with `C = real k / H_integral_1d` (`mollifier_1d_bound`) -- plain `integral_dominated_convergence`, no Hölder, no conjugate exponent, no `p=1` special case. This is NOT a loss for Theorem 3.2: the function actually mollified there is `\<^bold>f` = zero-extension of `f\<in>L^p[a,b]` off a BOUNDED interval, which is in `L^1` too (Hölder against the constant 1 on a finite-measure set -- add that small bridge lemma in piece 7).
- [ ] Piece 5: the translation-continuity chain (the big one -- indicator\<rightarrow>continuous\<rightarrow>simple\<rightarrow>general, then translation continuity).
  - [x] 5a `inner_regular_lborel`: `[A\<in>sets borel; emeasure lborel A \<noteq> \<infinity>; 0<e] \<Longrightarrow> obtains K where
        compact K, K\<subseteq>A, emeasure lborel (A-K) < ennreal e`. DONE, verified. (Derived from
        `outer_regular_lborel` on the complement inside `{-N..N}`; `K = {-N..N} - V` is compact via
        `compact_Icc` + `compact_Int_closed`. Needed `closed_Compl` for `closed (-V)`, and the
        `e/3`-split trick to dodge strict addition in `ennreal` -- see bug notes below.)
  - [x] 5b-i the tent function. DONE, verified (all six lemmas passed first try after the
        refactor below). **REFACTORED after 5 failed rounds of `obtains`/existential
        packaging (the MATH verified every time -- only the packaging failed).** Now a top-level
        `definition tent K d x = max 0 (1 - setdist {x} K / d)` plus standalone lemmas
        `tent_nonneg`, `tent_le_one` (`0<d`), `tent_continuous` (`0<d`), `tent_eq_one` (`x\<in>K`),
        `tent_near` (`compact K`, `K\<noteq>{}`, `0<d`, `tent K d x \<noteq> 0` \<Longrightarrow> `\<exists>y\<in>K. dist x y < d`),
        `tent_eq_zero_off` (off `U`, given `(\<Union>y\<in>K. ball y d) \<subseteq> U`), `tent_eq_zero_far`
        (given `\<bar>y\<bar>\<le>R0` on `K` and `R0+d < \<bar>x\<bar>`). **Call-site convention**: obtain `d` from
        `compact_subset_open_imp_ball_epsilon_subset[OF K_compact U_open K_sub_U]` and `R0` from
        `compact_imp_bounded` + `bounded_iff`/`real_norm_def`, then use `tent K d` directly as the
        approximating function -- no existential, no witness inference.
        **General lesson: prefer a named `definition` + separate property lemmas over any
        multi-witness `obtains`/`\<exists>` packaging in this project.**
  - [x] 5b-ii `indicator_continuous_approx`. DONE, verified.
        `\<lbrakk>0<p; A \<in> sets borel; emeasure lborel A \<noteq> \<infinity>; 0<e\<rbrakk> \<Longrightarrow>
         \<exists>g. continuous_on UNIV g \<and> (\<forall>x. 0 \<le> g x) \<and> (\<forall>x. g x \<le> 1)
             \<and> (\<exists>R. \<forall>x. R < \<bar>x\<bar> \<longrightarrow> g x = 0)
             \<and> integrable lborel (\<lambda>x. \<bar>g x - indicat_real A x\<bar> powr p)
             \<and> (LBINT x. \<bar>g x - indicat_real A x\<bar> powr p) < e`
        Structure: outer+inner regularity give `A \<subseteq> U` open and `K \<subseteq> A` compact with
        `emeasure lborel (U-K) < e`; a shared `key` gives the pointwise bound
        `\<bar>g x - indicat_real A x\<bar> powr p \<le> indicat_real (U-K) x` for ANY `g` that is
        0/1-bounded, `=1` on `K` and `=0` off `U`; a shared `wrap` turns that into
        integrability + the `< e` estimate; then case split `K={}` (witness `\<lambda>_. 0`)
        vs `K\<noteq>{}` (witness `tent K d`). NB the `blast` packaging at the end is FINE --
        it was wrongly blamed for the hang; see the `less_trans` bug class below.
  - [x] 5c `simple_dense_Lp`. DONE, verified.
        `\<lbrakk>0<p; f \<in> borel_measurable borel; integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p); 0<e\<rbrakk> \<Longrightarrow>
         \<exists>s. simple_function lborel s \<and> integrable lborel (\<lambda>x. \<bar>s x - f x\<bar> powr p)
             \<and> (LBINT x. \<bar>s x - f x\<bar> powr p) < e`
        Via `borel_measurable_implies_sequence_metric[OF f_meas', of 0]` (gives simple `s i`
        with `s i x \<longrightarrow> f x` and `\<bar>s i x\<bar> \<le> 2\<bar>f x\<bar>` for free), dominating function
        `w = 3 powr p * \<bar>f\<bar> powr p` (from `\<bar>s i x - f x\<bar> \<le> 3\<bar>f x\<bar>` + `powr_mono2` + `powr_mult`),
        pointwise `\<longrightarrow> 0` by `tendsto_powr2`, then `integral_dominated_convergence` and `LIMSEQ_D`.
        Also landed a reusable helper:
        `abs_powr_measurable: \<lbrakk>0<p; h \<in> borel_measurable lborel\<rbrakk> \<Longrightarrow>
         (\<lambda>x. \<bar>h x\<bar> powr p) \<in> borel_measurable lborel` -- use this instead of re-inlining the
        `continuous_on_powr'` + `measurable_compose` argument (it appears twice already).
  - [x] 5d-i `Lp_seminorm_sum` (finite-sum Minkowski). DONE, verified.
        `\<lbrakk>1\<le>p; finite I; \<And>i. i\<in>I \<Longrightarrow> h i \<in> borel_measurable M;
          \<And>i. i\<in>I \<Longrightarrow> integrable M (\<lambda>x. \<bar>h i x\<bar> powr p)\<rbrakk> \<Longrightarrow>
         integrable M (\<lambda>x. \<bar>\<Sum>i\<in>I. h i x\<bar> powr p)
         \<and> Lp_seminorm p M (\<lambda>x. \<Sum>i\<in>I. h i x) \<le> (\<Sum>i\<in>I. Lp_seminorm p M (h i))`
        Integrability MUST be carried in the same induction (each Minkowski step needs it for
        the partial sum). Induction stated with explicit \<open>\<longrightarrow>\<close>-form via a `for J` block.
  - [x] 5d-ii `simple_Lp_level_finite`. DONE, verified.
        `\<lbrakk>0<p; simple_function lborel s; integrable lborel (\<lambda>x. \<bar>s x\<bar> powr p); y\<noteq>0\<rbrakk> \<Longrightarrow>
         emeasure lborel (s -` {y} \<inter> space lborel) \<noteq> \<infinity>`
        Via `nn_integral_cmult_indicator` + `nn_integral_mono` against
        `integrable_iff_bounded`. This is what lets 5b-ii be applied to each level set.
  - [x] 5d-iii DONE, verified. Landed as THREE lemmas:
        `Lp_seminorm_scale: 0<p \<Longrightarrow> Lp_seminorm p M (\<lambda>x. c * h x) = \<bar>c\<bar> * Lp_seminorm p M h`;
        `indicator_scaled_Lp_approx: \<lbrakk>0<p; A \<in> sets borel; emeasure lborel A \<noteq> \<infinity>; 0<tau\<rbrakk> \<Longrightarrow>
         \<exists>gy. continuous_on UNIV gy \<and> integrable lborel (\<lambda>x. \<bar>y*(gy x - indicat_real A x)\<bar> powr p)
              \<and> Lp_seminorm p lborel (\<lambda>x. y*(gy x - indicat_real A x)) < tau`
         (no `y\<noteq>0` case needed: take the per-term tolerance `tau/(1+\<bar>y\<bar>)`);
        `simple_continuous_approx: \<lbrakk>1\<le>p; simple_function lborel s;
          integrable lborel (\<lambda>x. \<bar>s x\<bar> powr p); 0<e\<rbrakk> \<Longrightarrow> \<exists>g. continuous_on UNIV g \<and> \<dots> < e`;
        and the target
        `continuous_dense_Lp: \<lbrakk>1\<le>p; f \<in> borel_measurable borel;
          integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p); 0<e\<rbrakk> \<Longrightarrow> \<exists>g. continuous_on UNIV g
          \<and> integrable lborel (\<lambda>x. \<bar>g x - f x\<bar> powr p)
          \<and> Lp_seminorm p lborel (\<lambda>x. g x - f x) < e`.
        Used `bchoice` to get the family `G` of per-level-set approximants.
        NB `continuous_on_sum` has NO `finite I` premise -- `[OF finY]` raises THM 0.
  - [x] ~~old 5d-iii sketch~~ (kept for reference): 5c gives a simple `s` with
        `\<parallel>s-f\<parallel>\<^sub>p` small; `simple_function_indicator_representation_banach`
        (`Set_Integral.thy` line 1208) writes `s x = (\<Sum>y\<in>s`space M. indicator (s-`{y}\<inter>space M) x *\<^sub>R y)`;
        5d-ii gives each nonzero level set finite measure; 5b-ii approximates each indicator by a
        continuous compactly-supported `g\<^sub>y`; 5d-i sums the errors. Terms with `y=0` vanish, so
        restrict the sum to `s`space M - {0}`. Split the tolerance as `\<epsilon>/(2 * card * (1+\<bar>y\<bar>))`.
  - [ ] ~~5e `translation_continuous_Cc`, 5f `Lp_seminorm_translation_continuous`~~ -- NOT NEEDED
        for Theorem 3.2, see the route change above.
- [ ] Piece 6: **NO LONGER NEEDED FOR THEOREM 3.2 -- see the route change below.** (Still a
      worthwhile result on its own; leave it for later if ever.)
- [x] **Piece 7 DONE -- THEOREM 3.2 IS PROVED AND VERIFIED.** It lives in a NEW theory,
      `Lp_Approximation_General.thy` (imports `Lp_Approximation` + `Lp_Mollifiers`), rather than
      in `Lp_Approximation.thy`, so that no existing file had to be edited.
      `sigmoidal_Lp_approximation_theorem_general`:
      `\<lbrakk>sigmoidal \<sigma>; bounded_function \<sigma>; continuous_on UNIV \<sigma>; a<b;
        f \<in> borel_measurable borel; integrable (lebesgue_on {a..b}) (\<lambda>x. \<bar>f x\<bar> powr p);
        1\<le>p; 0<\<epsilon>\<rbrakk> \<Longrightarrow>
       \<exists>g. continuous_on {a..b} g \<and> (\<exists>N w. 0<w \<and> 0<N \<and>
         Lp_norm p a b (\<lambda>x. (\<Sum>k=2..N+1. (g(unif_part a b N ! k) - g(unif_part a b N ! (k-1)))
               * \<sigma>(w*(x - unif_part a b N ! k)))
             + g a * \<sigma>(w*(x - unif_part a b N ! 0)) - f x) < \<epsilon>)`
      Supporting bridges in the same file: `Lp_norm_eq_seminorm`, `powr_indicator_measurable`,
      `powr_indicator_integrable`, `integrable_powr_restrict`, `Lp_norm_le_lborel`,
      `integrable_powr_zero_extension`, `borel_measurable_lebesgue_on_real`,
      `sigmoidal_network_continuous`.

### Integration -- DONE (2026-09-03)

- [x] `Lp_Mollifiers` and `Lp_Approximation_General` added to
  `Sigmoid_Universal_Approximation.thy`'s import list. Full session build is GREEN:
  `isabelle build -d <afp>/Smooth_Manifolds -d "<Real and Complex Analytic>" -d . \
   Sigmoid_Universal_Approximation` \<rightarrow> exit 0, every theory 100%, 37 s session time
  (well inside the ROOT's `timeout = 600`), `document = pdf` also builds:
  `output/document.pdf`. `Lp_Mollifiers` 5.2 s, `Lp_Approximation_General` 2.8 s.
- Scratch heaps `Lp_Moll_Deps` and `Thm32_Deps` (~17 MB total, ROOTs under the session
  scratchpad, NOT in the project) exist purely for fast `eval_at`. Delete when done.
- KNOWN ODDITY, not diagnosed: `Lp_norm_eq_seminorm` (in `Lp_Approximation_General.thy`) is
  proved, but neither `rule` nor `simp` can apply it, even when the goal prints as exactly its
  own instance. Every use site instead inlines `unfolding Lp_norm_def Lp_seminorm_def by
  (rule refl)`, which works. The lemma is currently dead weight; worth a look.

### ROUTE CHANGE (found while starting 5d -- verified against the actual file, not assumed)

`sigmoidal_Lp_approximation_theorem` (Theorem 3.1, `Lp_Approximation.thy` line 73) assumes ONLY
`contin_f: "continuous_on {a..b} f"` (plus `sigmoidal \<sigma>`, `bounded_function \<sigma>`,
`continuous_on UNIV \<sigma>`, `a<b`, `p\<ge>1`, `0<\<epsilon>`). And `Lp_norm p a b g` is *definitionally*
`Lp_seminorm p (lebesgue_on {a..b}) g` -- compare `Lp_norm_def` (line 33) with
`Lp_seminorm_def` (`Lp_Inequalities.thy` line 20): identical modulo the measure argument, so
the "bridge" of old piece 7 step 1 is `by (simp add: Lp_norm_def Lp_seminorm_def)`.

Therefore Theorem 3.2 follows from **5d alone**, with NO mollifier convergence:
  `f \<in> L\<^sup>p[a,b]` \<rightarrow> (5d, continuous density) continuous `g` with `\<parallel>g-f\<parallel>\<^sub>p < \<epsilon>/2`
  \<rightarrow> (Thm 3.1 applied to `g`) `G\<^sub>N` with `\<parallel>G\<^sub>N g - g\<parallel>\<^sub>p < \<epsilon>/2` \<rightarrow> (Minkowski) `\<parallel>G\<^sub>N g - f\<parallel>\<^sub>p < \<epsilon>`.
Restricting is free: `\<parallel>\<cdot>\<parallel>_{L\<^sup>p[a,b]} \<le> \<parallel>\<cdot>\<parallel>_{L\<^sup>p(\<real>)}` for the zero-extension, so 5d on `lborel`
suffices. **Pieces 4, 5e, 5f and 6 are all unnecessary for Theorem 3.2.** The mollifier work in
`Mollifiers.thy` is not wasted -- it is a complete, verified development in its own right -- it
is just not on the critical path for THIS theorem.

## Standing rules (apply throughout, no exceptions)

1. **Never assume a proof works. Always verify via `isabelle eval_at` before moving on or reporting success.** Command template:
   ```
   cd /home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation && \
   isabelle eval_at -s -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys/Smooth_Manifolds \
     -d "/home/dusty/Desktop/Real and Complex Analytic" \
     -d /home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation \
     -l Real_and_Complex_Analytic <FILE>.thy <LINE>
   ```
   Always run via Bash with `run_in_background: true`, wait for the `<task-notification>`, then
   `grep -n "^Error\|Failed to\|Type unification\|Clash of types\|exited with code"` on the output
   file before reading further. A clean run ends with `exited with code 0` and no `Error at line`
   lines above it.
1b. **If an `eval_at` run takes much longer than the ~1-2 min norm, suspect LEAKED PROCESSES
   before suspecting a diverging tactic.** Each `eval_at` JVM holds `-Xmx4g`, and they do NOT
   always exit when their result is consumed -- three orphans from hours earlier were found still
   running (found via
   `ps -eo pid,etime,args | grep "Isabelle_Tool eval_at" | grep -v grep`), starving a later run to
   43 minutes with an empty output file. Kill stale ones by PID (match on the theory/line they
   reference so you don't kill the live run, and NEVER touch the user's `JEdit_Main` processes),
   then re-run. `free -g` is a quick sanity check. This is the same failure mode the project
   memory already records for orphaned `poly` processes.
1c. **USE THE PREBUILT DEPS HEAP -- iterations drop from minutes to ~19 seconds.** A scratch
   session `Lp_Moll_Deps` (parent `Real_and_Complex_Analytic`, theories `Mollifiers` +
   `Lp_Inequalities`) is built as a heap image, so `eval_at` no longer re-elaborates them.
   Its ROOT lives OUTSIDE the project (the project's own `ROOT` is untouched) at
   `<scratchpad>/deps/ROOT`; rebuild with `isabelle build -b -d ... -d <scratchpad>/deps
   Lp_Moll_Deps` if the heap is gone (takes ~20 s). Verification command becomes:
   ```
   cd /home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation && \
   isabelle eval_at -s -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys/Smooth_Manifolds \
     -d "/home/dusty/Desktop/Real and Complex Analytic" \
     -d <scratchpad>/deps -l Lp_Moll_Deps <FILE>.thy <LINE>
   ```
   **Do NOT also pass `-d .`** -- it collides with the `directories` entry in the scratch ROOT
   ("Duplicate use of directory"). Timing reference: whole 749-line `Lp_Mollifiers.thy` = ~19 s.
   So **anything over ~1 minute means a diverging tactic, not slow elaboration** -- bisect by
   running `eval_at` at successively earlier lines (this is how the `less_trans` hang was found
   in 4 probes). Note `Mollifiers.thy` alone elaborates in 5.7 s, so the deps were never the
   bottleneck -- do not blame them again.
2. **Re-read the file (or at least `wc -l` it) before every edit.** The user co-edits these files
   live in jEdit. Never assume your last-written version is still on disk. If the file changed
   underneath you, read the new content and build on it, don't overwrite.
3. **Work in small, individually-verified lemmas.** Every lemma below is sized to be one
   `eval_at` round (maybe 2-3 correction rounds). Do not write more than ~150 new lines before
   verifying. This project's own history (`mollifier-theory-scoping.md`) shows large unverified
   batches cost more total time than small verified ones.
4. **After landing and verifying a lemma, check off the box above and briefly note the final
   lemma name/statement next to it** (one line), so a fresh read of this file tells you exactly
   what exists without re-deriving it.
5. Update `/home/dusty/.claude/projects/-home-dusty-Desktop/memory/sigmoid-universal-approximation-formalization.md`
   with a short entry when a whole PIECE (not just one lemma) completes -- not after every single
   lemma, that memory file is already very long.

## Known recurring bug classes this session (check these FIRST when something fails)

- **`blast` DOES NO REWRITING -- if your statement differs from the cited lemma's by so much as
  `norm` vs `\<bar>\<dots>\<bar>`, it does not fail, it SEARCHES (10+ min).** `LIMSEQ_D` yields
  `norm (X n - L) < r`; writing the `obtain` with `\<bar>\<dots>\<bar>` instead hung the file. Fix: state the
  `obtain`/`have` in the cited lemma's EXACT syntactic form (`norm`), and convert afterwards in a
  separate `have \<dots> by simp`/`by linarith` step. Generalise: before `by blast`, eyeball the cited
  lemma's exact syntax; blast is for logical structure only.
- **Dominated convergence needs the sequence AND the limit to be NAMED constants.**
  `proof (rule integral_dominated_convergence)` fails with "Failed to apply initial proof method"
  when the goal is written `(\<lambda>i. \<integral>x. \<bar>s i x - f x\<bar> powr p \<partial>lborel) \<longlonglongrightarrow> (\<integral>x. 0 \<partial>lborel)`, and
  ALSO when only the sequence is named. Verified minimal pair in a scratch theory: with the limit
  a plain variable `f0` it goes through; with `integral\<^sup>L lborel (\<lambda>x. 0)` inline it does not.
  Fix: `define g where "g = (\<lambda>i x. \<dots>)"` AND `define f0 :: "real \<Rightarrow> real" where "f0 = (\<lambda>x. 0)"`
  (the type ascription on `f0` is required -- otherwise `0 :: 'a::zero` fails the
  `{second_countable_topology, real_normed_vector}` sort constraint), state the goal as
  `(\<lambda>i. integral\<^sup>L lborel (g i)) \<longlonglongrightarrow> integral\<^sup>L lborel f0`, and afterwards rewrite with
  `conv[unfolded f0_int]` where `f0_int: integral\<^sup>L lborel f0 = 0` -- NOT `by (simp add: f0_def)`,
  which diverges.
- **`by blast` with a TRANSITIVITY rule in the fact list diverges (does not terminate).**
  `have "emeasure lborel (U-K) < \<infinity>" using UK_small less_trans ennreal_less_top by blast`
  spun for 21 MINUTES at 106% CPU (one core pegged, RSS flat -- so it is a search loop, not a
  memory or leak problem) before being killed. Handing `blast` a transitivity lemma lets it chain
  `<` steps without bound. **Fix: apply the transitivity yourself and leave `blast` out** --
  `using less_trans[OF UK_small ennreal_less_top] by simp`. Cost after the fix: 19 seconds for
  the whole file. NB the SAME pattern at `measure_lt_of_emeasure_lt` (`using lt less_trans
  ennreal_less_top by blast`) happens to terminate because its context is tiny -- it is a latent
  landmine, not a counterexample. Whenever an `eval_at` run exceeds ~1 min, grep the new text for
  `less_trans`/`order_trans`/`le_less_trans` sitting in a `using ... by blast`.
- **`simp`/`auto` silently DISCARD a supplied bound that it can prove on its own**, then fail on
  the goal that needed it. `show ?thesis using a0 a1 b0 b1 by (simp add: abs_le_iff)` failed with
  residual `\<lbrakk>0 \<le> g x; g x \<le> 1\<rbrakk> \<Longrightarrow> g x - ind \<le> 1 \<and> ind - g x \<le> 1` -- the two `indicat_real`
  bounds `b0`,`b1` were rewritten to `True` and dropped. Fix: state the two halves explicitly as
  their own `have`s (in the form the residual shows, i.e. already `-`-normalised) and feed those.
- **`\<forall>`-quantified `using` facts are not instantiated by `simp`/`auto`** -- write
  `g0[rule_format]` (or `spec[OF g0]`) to get the instance first. Cost this session: one round.
- **`indicat_real A x = 0` does NOT follow by `auto` from `x \<notin> U` and `A \<subseteq> U`** ("Failed to apply
  initial proof method"). Derive `x \<notin> A` by `blast` first, then `by simp` closes the indicator.
- **`arg_cong` for `powr` arguments**: `simp` does NOT reliably rewrite a compound expression
  inside a `powr` base or exponent using a supplied plain equation (`using eq_fact by simp`),
  even when the equation is exactly what's needed -- it silently normalizes one side differently
  (e.g. `(a+b)/2` vs `a/2+b/2`) and leaves a bizarre unrelated-looking residual. Fix: always use
  `arg_cong[OF eq_fact, of "\<lambda>t. t powr p"]` (or `\<lambda>e. base powr e` for the exponent) to bridge,
  never `using eq_fact by simp`.
- **`powr_powr` exponent cancellation silently needs `p\<noteq>0`**: `(x powr a) powr b = x powr(a*b)`
  is unconditional, but simplifying `a*b` to `1` (e.g. `(1/p)*p=1`) needs `p\<noteq>0`/`p>0` supplied
  explicitly via `using p_gt1 ... by (simp add: powr_powr)` -- easy to forget since the goal
  *looks* like it should just work.
- **`simp add: mult_left_mono` / `mult_right_mono` does not reliably close a raw multiplicative
  inequality goal.** Use `proof (rule mult_left_mono) show "..." ... show "0 \<le> ..." ... qed`
  instead, with named subgoals.
- **`field_simps` on an equality mixing two related-but-syntactically-distinct atoms** (e.g.
  `2 powr p` and `2 powr (p-1)` in the same goal) leaves a residual needing the relating fact
  applied as an explicit substitution first (`arg_cong`-style), not as an extra `using` fact fed
  to `field_simps`.
- **A genuinely polymorphic constant needs its domain type pinned on the FIRST occurrence of every
  fresh `have`/`obtain`/`show`** -- not applicable here (no more `'n::finite`/`vec` in this file,
  everything is plain `real`), but if you find yourself importing anything from `Mollifiers.thy`
  and citing its `'n`-polymorphic lemmas, this still applies to those citations.
- **`Bochner_Integration.integrable_bound`/`integral_mono_AE` need the domination as an `AE` fact**
  (`(AE x in M. norm(g x)\<le>norm(f x))`), not a bare `\<And>x. ...` -- wrap with `(intro AE_I2) ...`.
- **`show "..."` text inside `proof (rule ...)` can pick up its own unconnected type/schematic**
  even when the surrounding goal is already pinned -- if a `show` with a fresh bound variable
  (`\<forall>t\<in>S. ...`) fails with a bizarre residual, ascribe the type via the SET (`\<forall>t\<in>(UNIV::real
  set). ...`) rather than the binder.
- **`obtains`-style `show ?thesis using that[OF f1 f2 ...] .` fails with `OF: no unifiers` whenever
  any of the supplied facts has a BOUND VARIABLE.** After a `have "\<And>x. P x"` is discharged, the
  fact is exported with a SCHEMATIC `?x` (`P ?x`), but `that` expects a meta-quantified premise
  (`\<And>x. P x`), and `OF` will not bridge the two. Fix: use
  `show ?thesis proof (rule that) show "\<And>x. P x" by (rule my_fact) ... qed` instead -- each
  subgoal comes out in the `\<And>x.` form and `rule` instantiates the schematic fine. `that[OF ...]`
  IS fine when every supplied fact is closed (no bound variables) -- e.g. it works in
  `inner_regular_lborel`, which supplies only `compact K`, `K \<subseteq> A`, and a measure bound.
  **AND: `rule that` alone is not enough either** -- it leaves the `obtains` variables schematic
  (`?g`, `?R`) across ALL the subgoals, and Isar's `show` refuses to commit a schematic shared
  between pending goals, giving the unhelpful "Failed to refine any pending goal". **AND
  `that[of g "R0+d"]` fails too**, on argument order/type ("Cannot generate coercion from real to
  'a"). **CONCLUSION, learned the hard way over four rounds on `tent_function`: when a result has
  SEVERAL witnesses and its properties mention bound variables, do NOT use `obtains` at all.**
  State the conclusion as an explicit `shows "\<exists>g R. P g R \<and> (\<forall>x. Q g x) \<and> ..."`, finish the proof
  with one `have "<the big conjunction, witnesses substituted>" using <the named haves> by blast`
  followed by `then show ?thesis by blast`, and `obtain` at the CALL site instead. The mathematics
  was never the problem here -- all six component `have`s verified on every one of the four
  attempts; only the `obtains` plumbing failed.
- **A bounded existential `\<exists>y\<in>K. P y` may not be closed by `auto` even with the witness and all
  facts in context** -- use `proof (rule bexI[of _ y]) show "P y" ... show "y \<in> K" ... qed`.
- If genuinely stuck (3+ failed rounds on the same lemma), reread the actual `eval_at` error text
  character-by-character before trying another tactic -- most fixes this whole project came from
  reading the residual goal precisely, not from guessing a different tactic.

## Confirmed lemma reference (exact names/signatures found this session -- use these, don't re-search)

- `Youngs_inequality` (`HOL-Analysis.Convex`): `[p>1;q>1;1/p+1/q=1;a\<ge>0;b\<ge>0] \<Longrightarrow> a*b \<le> a powr p/p + b powr q/q`.
- `powr_convex` (`HOL-Analysis.Convex`): `p\<ge>1 \<Longrightarrow> convex_on {0<..} (\<lambda>x. x powr p)`.
- `convex_onD`: `convex_on A f \<Longrightarrow> [t\<ge>0;t\<le>1;x\<in>A;y\<in>A] \<Longrightarrow> f((1-t)*\<^sub>Rx+t*\<^sub>Ry) \<le> (1-t)*f x+t*f y`.
- `powr_mono2`: `[0\<le>a;0\<le>x;x\<le>y] \<Longrightarrow> x powr a \<le> y powr a`.
- `powr_diff`: `w powr(z1-z2) = w powr z1/w powr z2` (unconditional).
- `powr_mult`: `(x*y) powr a = x powr a * y powr a` (unconditional).
- `powr_ge_zero [simp]`: `0 \<le> x powr y` (unconditional).
- `powr_eq_0_iff [simp]`: `w powr z = 0 \<longleftrightarrow> w = 0`.
- `Lp_seminorm p M g = (\<integral>x. \<bar>g x\<bar> powr p \<partial>M) powr (1/p)` (`Lp_Inequalities.thy`).
- `Lp_Holder_inequality`: `[p>1;q>1;1/p+1/q=1;f\<in>borel_measurable M;g\<in>borel_measurable M;
  integrable M(\<lambda>x.\<bar>f x\<bar> powr p);integrable M(\<lambda>x.\<bar>g x\<bar> powr q)] \<Longrightarrow>
  (\<integral>x.\<bar>f x*g x\<bar>\<partial>M) \<le> Lp_seminorm p M f * Lp_seminorm q M g`.
- `Lp_Minkowski_inequality`: `[p\<ge>1;f,g\<in>borel_measurable M;integrable M(\<lambda>x.\<bar>f x\<bar>powr p);
  integrable M(\<lambda>x.\<bar>g x\<bar>powr p)] \<Longrightarrow> Lp_seminorm p M(\<lambda>x.f x+g x) \<le> Lp_seminorm p M f+Lp_seminorm p M g`.
- `outer_regular_lborel`: `[B\<in>sets borel;0<e] \<Longrightarrow> \<exists>U. open U \<and> B\<subseteq>U \<and> emeasure lborel(U-B)<e`
  (obtains-style; `B\<in>sets borel`, use `sets_lborel`/`sets_completionI_sets` to bridge from
  `sets lebesgue` if needed).
- `continuous_on_setdist [continuous_intros]`: `continuous_on T (\<lambda>y. setdist {y} S)`.
- `setdist_pos_le [simp]`: `0 \<le> setdist S T`.
- `setdist_gt_0_compact_closed` (`Topology_Euclidean_Space.thy`, line ~2411) -- FOUND, no need to
  prove: `[compact S; closed T] \<Longrightarrow> (setdist S T > 0 \<longleftrightarrow> (S\<noteq>{} \<and> T\<noteq>{} \<and> S\<inter>T={}))`. NB it is an
  IFF with NONEMPTINESS on the right: for the tent-function construction you must separately
  handle `K={}` (then the approximating `g` is just `0`, and the bound still holds since
  `measure(U\<setminus>K)=measure U` is already small) and show `-U\<noteq>{}` (true because `U` has finite
  measure -- `measure U \<le> measure A + \<epsilon> < \<infinity>` -- while `UNIV::real set` does not).
- `separate_compact_closed` (`Elementary_Metric_Spaces.thy` ~2258) is the `\<exists>d>0. \<forall>x\<in>S. \<forall>y\<in>T.
  d \<le> dist x y` form of the same fact, if that shape is more convenient.
- `borel_measurable_implies_sequence_metric` (`Bochner_Integration.thy`, used internally to build
  Bochner integration): `f\<in>borel_measurable M \<Longrightarrow> \<exists>s. (\<And>i. simple_function M(s i)) \<and>
  (\<And>x. x\<in>space M \<Longrightarrow> (\<lambda>i. s i x)\<longlonglongrightarrow>f x) \<and> (\<And>i x. x\<in>space M \<Longrightarrow> norm(s i x)\<le>2*norm(f x))`
  (exact obtains-form, check `Bochner_Integration.thy` line ~1223 for the precise pattern used
  inside `integrableI_bounded`'s own proof -- copy that citation style).
- `mollifier_1d_integral_one`, `mollifier_1d_nonneg`, `mollifier_1d_support`,
  `convolution_1d_apply` -- all in `Lp_Mollifiers.thy`, already proved, use directly.
- `lborel_integral_translation`, `lborel_integral_reflect_translate` (`Mollifiers.thy`, generic
  over `'a::euclidean_space`, directly usable at `'a:=real` since `Lp_Mollifiers.thy` imports
  `Mollifiers`).
- `Lp_norm p a b g = (\<integral>x.\<bar>g x\<bar> powr p \<partial>(lebesgue_on {a..b})) powr(1/p)` (`Lp_Approximation.thy`).
- `sigmoidal_Lp_approximation_theorem` (Theorem 3.1, `Lp_Approximation.thy`): for `f` CONTINUOUS
  on `{a..b}`, `p\<ge>1`, gives `\<exists>N w. Lp_norm p a b (\<lambda>x. G_N f x - f x) < \<epsilon>`. Re-read its exact
  hypotheses in the file before citing -- don't rely on this summary's paraphrase for the exact
  Isar text.

## Detailed build plan

### Piece 3: basic `mollifier_1d` facts (`Lp_Mollifiers.thy`)

Mirror `Mollifiers.thy`'s `mollifier_continuous`, `mollifier_measurable`, `mollifier_bound`
directly (these are short, ~10-15 lines each in the original, purely about `mollifier_1d` itself,
no convolution yet):
- `mollifier_1d_continuous: continuous_on UNIV (mollifier_1d k)`
- `mollifier_1d_measurable: mollifier_1d k \<in> borel_measurable borel`
- `mollifier_1d_bound: mollifier_1d k x \<le> real k / H_integral_1d` (from `Bump_Function.H_range(2)`)

### Piece 4: continuity of `convolution_1d` for general `f \<in> L^p` (NEW technique, not in `Mollifiers.thy`)

`Mollifiers.thy`'s `convolution_continuous` needed `f` BOUNDED -- wrong hypothesis for Theorem
3.2. Instead, for FIXED `k`, prove continuity via Hölder (conjugate `q`, `1/p+1/q=1` -- for
`p=1` this needs `q=\<infinity>`/a separate trivial argument since `mollifier_1d k` is itself bounded and
compactly supported, handle `p=1` as its own easy case using boundedness of `mollifier_1d` alone,
not Hölder):

```
lemma convolution_1d_continuous:
  fixes f :: "real \<Rightarrow> real" and k :: nat and p :: real
  assumes k_pos: "k > 0" and p_ge1: "p \<ge> 1"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_intp: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "continuous_on UNIV (mollifier_1d k \<star>\<^sub>1 f)"
```

Strategy: `continuous_on_sequentiallyI` (same entry point `Mollifiers.thy` used), for `u_n \<rightarrow> a`
show `(mollifier_1d k \<star>\<^sub>1 f)(u_n) \<rightarrow> (mollifier_1d k \<star>\<^sub>1 f)(a)`. Bound the difference via Hölder
applied to `f` and `h_n(y) := mollifier_1d k(u_n-y) - mollifier_1d k(a-y)`:
`|\<integral>y h_n(y) f(y) dy| \<le> Lp_seminorm q lborel h_n * Lp_seminorm p lborel f`. Since `u_n,a` range over
a bounded set (convergent sequence) and `mollifier_1d k` has compact support (radius `2/k`),
`h_n` is supported in a FIXED bounded region for all `n`, uniformly bounded (mollifier_1d is
bounded, piece 3), and `h_n \<rightarrow> 0` pointwise (continuity of `mollifier_1d k`, piece 3) -- so
`Lp_seminorm q lborel h_n \<rightarrow> 0` by ORDINARY dominated convergence on a finite-measure region
(same pattern as `mollifier_convolution_L1_convergence` in `Mollifiers.thy`, just with `h_n`
playing the role that `mollifier(Suc k)\<star>f - f` played there). `Lp_seminorm p lborel f` is a
fixed finite constant (from `f_intp`), so the product `\<rightarrow>0`.

For `p=1`: `q` doesn't exist as a finite conjugate; instead directly bound `|\<integral>y h_n(y)f(y)dy| \<le>
(\<integral>y|h_n(y)|dy) * (sup|f| on the bounded support region)`... actually `f` need not be bounded
even locally for `p=1`. Better: for `p=1` don't use Hölder at all -- bound `|\<integral>h_n f| \<le> \<integral>|h_n||f|
\<le> (sup|h_n|) \<integral>_{support}|f|` using `mollifier_1d`'s own uniform continuity (piece 3, or derive
it) to make `sup|h_n|\<rightarrow>0`, and `\<integral>_{support}|f|` is a FIXED finite number (integrability of `f`
over the fixed bounded support region, from `f\<in>L^1`). Write this `p=1` case ONLY if it turns out
Theorem 3.2 actually needs `p=1` invoked here -- check whether Theorem 3.1's own `p\<ge>1` hypothesis
already forces you to handle it, or whether you can WLOG require `p>1` in this specific lemma and
handle `p=1` as a trivial wrapper later. Don't over-build this case before confirming it's needed.

### Piece 5: translation-continuity chain

This is the large one from the scoping message already given to the user. Sub-lemmas, in order,
each its own `eval_at` round:

1. `compact_closed_positive_setdist` (find the real name first via `grep -rn
   "separate_compact_closed\|compact.*closed.*setdist\|setdist.*compact.*closed"
   /home/dusty/Desktop/Isabelle/Isabelle2025-2/src/HOL/Analysis/*.thy` -- if it exists, just cite
   it, don't reprove).
2. `indicator_continuous_approx`: `A \<in> sets lebesgue \<Longrightarrow> measure lborel A < \<infinity> \<Longrightarrow> e > 0 \<Longrightarrow>
   \<exists>g. continuous_on UNIV g \<and> (\<integral>x. \<bar>g x - indicat_real A x\<bar> powr p \<partial>lborel) < e` -- via outer
   regularity (twice: once for `A`, once for a bounded complement to get inner/compact
   approximation -- see the plan message already sent to the user for the exact construction),
   then the `setdist`-based tent function.
3. `simple_dense_Lp`: for `f \<in> borel_measurable borel`, `integrable lborel(\<lambda>x.\<bar>f x\<bar> powr p)`,
   `\<exists>s. simple_function borel s \<and> Lp_seminorm p lborel (\<lambda>x. s x - f x) < e` -- via
   `borel_measurable_implies_sequence_metric` + dominated convergence (as scoped).
4. `continuous_dense_Lp`: combine 2+3 via the finite-sum/Minkowski argument.
5. `translation_continuous_Cc`: for `g` continuous with compact support, `Lp_seminorm p lborel
   (\<lambda>x. g(x+h)-g x) \<rightarrow> 0` as `h\<rightarrow>0` -- via uniform continuity on a compact set containing the
   support plus a margin.
6. `Lp_seminorm_translation_continuous`: the target -- combine 4+5 via a 3-\<epsilon> argument, using
   `lborel_integral_translation` (already available, imported from `Mollifiers.thy`) for the
   translation-invariance step.

### Piece 6: main convergence theorem

```
theorem mollifier_1d_Lp_convergence:
  fixes f :: "real \<Rightarrow> real" and p :: real
  assumes p_ge1: "p \<ge> 1"
  assumes f_meas: "f \<in> borel_measurable borel"
  assumes f_intp: "integrable lborel (\<lambda>x. \<bar>f x\<bar> powr p)"
  shows "(\<lambda>k. Lp_seminorm p lborel (\<lambda>x. (mollifier_1d k \<star>\<^sub>1 f) x - f x)) \<longlonglongrightarrow> 0"
```
Via the pointwise Hölder bound (`|\<rho>_k*f(x)-f(x)|^p \<le> \<integral>y \<rho>_k(y)|f(x-y)-f(x)|^p dy`, derived the
same way `Lp_Holder_inequality` itself was derived from Young's -- see the plan message) +
Fubini/Tonelli + `Lp_seminorm_translation_continuous` (piece 5) for the "near" part and
`mollifier_1d_support`'s shrinking support for the "far" part, mirroring
`mollifier_pointwise_limit`'s near/far split but applied to `\<parallel>\<sqdot>\<parallel>_p` as a function of the shift
`y` rather than pointwise in `x`.

### Piece 7: Theorem 3.2 assembly (`Lp_Approximation.thy`)

1. Bridge `Lp_norm p a b g` to `Lp_seminorm p (lebesgue_on {a..b}) g` (should be near-definitional,
   check `Lp_norm_def` matches `Lp_seminorm_def` exactly modulo the measure argument).
2. Define `\<^bold>f x = (if x\<in>{a..b} then f x else 0)` (paper's own `fe`), show `\<^bold>f \<in> borel_measurable
   borel` and `integrable lborel (\<lambda>x.\<bar>\<^bold>f x\<bar> powr p)` from `f`'s `Lp_norm`-integrability on `{a..b}`.
3. Apply piece 6 to `\<^bold>f` to get `f_n := mollifier_1d n \<star>\<^sub>1 \<^bold>f \<rightarrow> \<^bold>f` in `Lp_seminorm p lborel`,
   hence (monotonicity of the integral, restricting `lborel` to `lebesgue_on{a..b}`) `\<rightarrow> \<^bold>f = f` in
   `Lp_norm p a b` too.
4. `f_n` continuous on `UNIV` (piece 4) hence on `{a..b}`, apply `sigmoidal_Lp_approximation_theorem`
   (Theorem 3.1) to get `G_N f_n \<rightarrow> f_n` in `Lp_norm p a b`.
5. Combine via `Lp_Minkowski_inequality` (bridged to `Lp_norm` via step 1) exactly as the paper
   does: pick `n` from step 3 for `\<epsilon>/2`, then `N,w` from step 4 (Theorem 3.1) for `\<epsilon>/2` at that
   fixed `n`, conclude `Lp_norm p a b (\<lambda>x. G_N f_n x - f x) < \<epsilon>`.

## Efficiency notes

- Do NOT re-derive anything already in the "Confirmed lemma reference" section above -- cite it.
- Do NOT rebuild `outer_regular_lborel`, `Youngs_inequality`, `powr_convex`,
  `borel_measurable_implies_sequence_metric`, or any Bochner/dominated-convergence machinery from
  scratch -- all confirmed to exist.
- If a sub-piece turns out to need something NOT in the confirmed-lemma list, search for it
  FIRST (grep across `/home/dusty/Desktop/Isabelle/Isabelle2025-2/src/HOL/Analysis/*.thy`) before
  assuming it needs proving -- this session found several "surely this needs building" pieces
  (Young's inequality, `powr_convex`, simple-function density with domination) already sitting in
  core HOL-Analysis.
- When a lemma needs 3+ correction rounds, stop and re-read this file's bug-class list before
  trying a 4th tactic guess.
