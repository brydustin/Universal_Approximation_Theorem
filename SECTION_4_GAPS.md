# Section 4 gaps: Theorem 4.1 (general `j`) and Theorem 4.2

> **SECTION 4 PROOF MILESTONE 2026-09-05.** The three developments below are proved.
> This historical milestone does not establish whole-paper fidelity; the later
> `PAPER_AUDIT_2026-09-05.md` identified specification differences and missing
> corollary assemblies. Current repairs are tracked in `PAPER_FIXES_TODO.md`.
> No `sorry`/`oops`/`axiomatization`/`consts` anywhere in the project (19 theories, 17,246 lines,
> 347 results); the session builds exit 0 with PDF in ~60 s. The three top-level results:
>
> - `forward_diff_consistency` (`Forward_Difference_Consistency.thy`) — eq. (4.4), general `j`
> - `forward_diff_simultaneous_approximation` (`Simultaneous_Approximation_General_j.thy`) —
>   **Theorem 4.1**, general `j`, with the genuine simultaneity quantifier
> - `forward_diff_rate` (same file) — **Theorem 4.2**, general `j`;
>   `forward_diff_one_rate` (`Simultaneous_Approximation_Rate.thy`) is the `j=1` case by a
>   different route
>
> The rest of this file is a historical working record, including superseded status notes.

Audit date: 2026-09-04. Companion to `THEOREM_3_2_PLAN.md` (Sections 3/5, now closed).

Historical status before the fidelity audit (superseded): No `sorry`, `oops`,
`axiomatization` or `consts` anywhere in the 17 theories / 13,712 lines / 289 results, and the
session builds exit 0. The n-dimensional scope of Section 5 alone does not imply
the paper's result, because its sampling operator also differed. See the current checklist.

---

## What the paper actually says

Both statements transcribed from Costarelli & Spigler, *Anal. Theory Appl.* **29** (2013),
pp.176 (Thm 4.1), p.178 (eq. 4.4), p.180 (Thm 4.2).

### (4.2) — the forward difference operator

```
    \<Delta>\<^sup>j\<^sub>k f  :=  (1/h\<^sup>j) \<Sum>\<^sub>v\<^sub>=\<^sub>0\<^sup>j  (j choose v) (-1)\<^sup>v f(x\<^sub>k\<^sub>+\<^sub>j\<^sub>-\<^sub>v)
```

for `j \<in> \<nat>`, `j \<le> N`, `k = 0,1,\<dots>,N-j`. **Formalized**: `forward_diff` in
`Derivative_Approximation.thy:140`, indexed by the partition list `xs` and mesh `h` directly.

### (4.3) — the network `G\<^sup>j\<^sub>N f`

```
    (G\<^sup>j\<^sub>N f)(x) := \<Sum>\<^sub>k\<^sub>=\<^sub>1\<^sup>N\<^sup>-\<^sup>j (\<Delta>\<^sup>j\<^sub>k f - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1 f) \<sigma>(w(x - x\<^sub>k))  +  \<Delta>\<^sup>j\<^sub>0 f \<cdot> \<sigma>(w(x - x\<^sub>-\<^sub>1))
```

**Formalized**: `Gj_network` in `Derivative_Approximation.thy:1075`.

### Theorem 4.1 (p.176)

> Let `\<sigma>` be a bounded sigmoidal function and let `f \<in> \<Ccirc>\<^sup>n\<^sup>+\<^sup>1[a,b]`, `n \<in> \<nat>\<^sup>+`, be fixed. For every
> `\<epsilon> > 0`, there exist `N \<in> \<nat>\<^sup>+` and `w > 0` (depending on `N`), such that **for every
> `j = 1,\<dots>,n`**, [defining `G\<^sup>j\<^sub>N f` by (4.3)] we have `\<parallel>G\<^sup>j\<^sub>N f - f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity> < \<epsilon>`.

Note the quantifier order: **one `N` and one `w` serve every `j` at once.** That simultaneity is
the actual content of the word "simultaneous" in the theorem's title, and it is *not* implied by
proving the `j`-th case separately for each `j`.

### (4.4) — the finite-difference consistency estimate (p.178)

> We now observe that, for every `k = 0,1,\<dots>,N-j`, the terms `\<Delta>\<^sup>j\<^sub>k f` provide an approximation to
> `f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k)`, obtained by forward finite differences. **It is well known that** there exists a
> positive constant `C\<twiddle>\<^sub>j > 0`, depending only on `f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)`, such that
> ```
>     |\<Delta>\<^sup>j\<^sub>k f - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k)| \<le> C\<twiddle>\<^sub>j h = C\<twiddle>\<^sub>j (b-a)/N =: C\<^sub>j/N
> ```
> for every `k = 0,1,\<dots>,N-j`.

**"It is well known" = the paper does not prove this.** It is cited, not derived. So a faithful
formalization has to supply the proof itself; this is genuine mathematical content, not
transcription. It is also the load-bearing lemma for *both* remaining gaps.

### Theorem 4.2 (p.180)

> Let `\<sigma>` be a bounded sigmoidal function, `f \<in> \<Ccirc>\<^sup>n\<^sup>+\<^sup>1[a,b]`, `n \<in> \<nat>\<^sup>+`, and `j = 1,\<dots>,n` be fixed. For
> every `N \<in> \<nat>\<^sup>+`, `N > j+3`, there exists `w\<oline> > 0` (depending on `N`) such that for every
> `w \<ge> w\<oline>` and `G\<^sup>j\<^sub>N f` defined in (4.3) with `w`, we have
> ```
>   \<parallel>G\<^sup>j\<^sub>N f - f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity> < (1/N) [ L\<^sub>j(b-a)(2\<parallel>\<sigma>\<parallel>\<^sub>\<infinity> + 1 + max{2,j})
>                            + C\<twiddle>\<^sub>j(b-a)(4\<parallel>\<sigma>\<parallel>\<^sub>\<infinity> + 3) + \<parallel>f\<^sup>(\<^sup>j\<^sup>)\<parallel>\<^sub>\<infinity> ]
> ```
> where `C\<twiddle>\<^sub>j > 0` is a constant depending only on `f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)` and `L\<^sub>j > 0` is the Lipschitz constant
> for `f\<^sup>(\<^sup>j\<^sup>)`.

Structurally 4.2 stands to 4.1 exactly as **Theorem 5.2 stands to Theorem 5.1**: same `J\<^sub>1`/`J\<^sub>2`
case split, but every `\<eta>` replaced by an explicit constant. That parallel is the main reason to
be optimistic about the effort here — the 5.1 \<rightarrow> 5.2 refactor was completed on 2026-09-04 and the
playbook is known (see "Gotchas hit while proving 5.2" in `THEOREM_3_2_PLAN.md`).

---

## What is formalized, precisely

| Paper object | Isabelle | Status |
|---|---|---|
| (4.2) `\<Delta>\<^sup>j\<^sub>k f` | `forward_diff f xs h j k` | complete, general `j` |
| (4.3) `G\<^sup>j\<^sub>N f` | `Gj_network \<sigma> f xs h N j w x` | complete, general `j` |
| `G\<^sup>j\<^sub>N f` continuity | `Gj_network_continuous` | complete, general `j` |
| (4.4) | `forward_diff_one_error_bound` | **`j=1` only**, constant `M/2` |
| (4.4) | `forward_diff_two_error_bound` | **`j=2` only**, constant `5M/3` |
| (4.4) | `forward_diff_three_error_bound` | **`j=3` only**, constant `11M/2` |
| (4.4) | `forward_diff_four_error_bound` | **`j=4` only**, constant `274M/15` |
| **Theorem 4.1** | `forward_diff_one_approximation` | **`j=1` only** |
| **Theorem 4.2** | — | **absent** |
| Cor 6.1(ii) logistic | `logistic_approximation_theorem_derivative` | `j=1` instance only |
| Cor 6.2(ii) Gompertz | `gompertz_approximation_theorem_derivative` | `j=1` instance only |

The four (4.4) instances were each obtained by a separate hand-rolled Taylor expansion
(`forward_diff_{one,two,three,four}_taylor`). Note how the constants blow up — `M/2`, `5M/3`,
`11M/2`, `274M/15`. They are not of the form the paper's `C\<twiddle>\<^sub>j` predicts, because each was
optimized ad hoc rather than derived from a uniform argument. **This route does not scale and
should be superseded, not extended.**

---

## Gap 1: (4.4) for general `j` — the tractable, load-bearing piece

### The mathematics

The paper's `C\<twiddle>\<^sub>j` is `j \<cdot> \<parallel>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<parallel>\<^sub>\<infinity>`, and the clean derivation avoids both divided differences
and iterated integrals. Write `D\<^sub>h g x := (g(x+h) - g(x))/h`. Then:

1. **`\<Delta>\<^sup>j\<^sub>k f = (D\<^sub>h\<^sup>j f)(x\<^sub>k)`** — the binomial sum (4.2) is the `j`-fold iterate of `D\<^sub>h`. Induction
   on `j` via Pascal's rule (`binomial_Suc_Suc`).
2. **`D\<^sub>h` commutes with `deriv`**: `deriv (D\<^sub>h g) = D\<^sub>h (deriv g)`, hence
   `(deriv^^m) (D\<^sub>h g) = D\<^sub>h ((deriv^^m) g)`.
3. **MVT**: `D\<^sub>h g x = g'(\<eta>)` for some `\<eta> \<in> (x, x+h)`; so `|D\<^sub>h g x| \<le> sup|g'|`.
4. **Induction on `j`** for the bound itself. With `M` bounding `|f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)|`:
   - IH applied to `g := D\<^sub>h f` (whose `j`-th derivative is `D\<^sub>h(f\<^sup>(\<^sup>j\<^sup>))`, bounded by `M` via step 3):
     `|(D\<^sub>h\<^sup>j f)(x) - (D\<^sub>h f)\<^sup>(\<^sup>j\<^sup>-\<^sup>1\<^sup>)(x)| \<le> (j-1) M h`
   - step 2 + step 3 on `f\<^sup>(\<^sup>j\<^sup>-\<^sup>1\<^sup>)`: `(D\<^sub>h f)\<^sup>(\<^sup>j\<^sup>-\<^sup>1\<^sup>)(x) = D\<^sub>h(f\<^sup>(\<^sup>j\<^sup>-\<^sup>1\<^sup>))(x) = f\<^sup>(\<^sup>j\<^sup>)(\<eta>)`, and MVT once more on
     `f\<^sup>(\<^sup>j\<^sup>)` gives `|f\<^sup>(\<^sup>j\<^sup>)(\<eta>) - f\<^sup>(\<^sup>j\<^sup>)(x)| \<le> M h`
   - total `\<le> j M h`. \<box>

Only `MVT` (`HOL/Deriv.thy:1654`) is needed — no interpolation theory, no nested integrals, no
new AFP dependency. (Checked: AFP `Polynomial_Interpolation/Newton_Interpolation.thy` is exact
interpolation over rings, with no analytic error term — not applicable, and adding it risks
another class clash of the `Lp`/`Smooth_Manifolds` kind.)

### Target statement

```isabelle
lemma forward_diff_error_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes h_pos: "0 < h"
  assumes Ck:    "C_k_on (Suc j) f U"
  assumes seg:   "{x0..x0 + real j * h} \<subseteq> U"
  assumes bound: "\<And>t. t \<in> {x0..x0 + real j * h} \<Longrightarrow> \<bar>(deriv ^^ Suc j) f t\<bar> \<le> M"
  shows "\<bar>(D_h ^^ j) f x0 - (deriv ^^ j) f x0\<bar> \<le> real j * M * h"
```
plus the bridge `forward_diff f xs h j k = (D_h ^^ j) f (xs ! k)` for uniform `xs`, giving (4.4)
in the paper's own notation with `C\<twiddle>\<^sub>j = j \<cdot> M`.

### Checklist — **GAP 1 CLOSED 2026-09-04**, all verified, capstone green

New file `Forward_Difference_Consistency.thy` (imports `Derivative_Approximation`), ~625 lines.

- [x] A1. `Dh h g x = (g (x+h) - g x) / h`; `binom_pascal_sum` (the Pascal identity, isolated from
      all analysis) and `Dh_iterate_sum`:
      `(Dh h ^^ j) g x = (1/h^j) * (\<Sum>v\<in>{0..j}. real (j choose v) * (-1)^v * g (x + (real j - real v)*h))`
- [x] A2. `Ush h U = U \<inter> {t. t + h \<in> U}` with `Ush_open`; `Dh_has_derivative` (DERIV form),
      `deriv_Dh`, and the iterate `higher_deriv_Dh`:
      `\<forall>t\<in>Ush h U. (deriv^^m) (Dh h g) t = Dh h ((deriv^^m) g) t`
- [x] A3. `Dh_mvt`: `\<exists>\<eta>. x<\<eta> \<and> \<eta><x+h \<and> Dh h g x = g' \<eta>`; `Dh_abs_bound`: `\<bar>Dh h g x\<bar> \<le> M`
- [x] A4. **not needed** — superseded by a better hypothesis form. `higher_deriv_Dh` and the main
      induction take the *unpacked derivative chain*
      (`\<And>i t. i<k \<Longrightarrow> t\<in>U \<Longrightarrow> ((deriv^^i) g has_real_derivative (deriv^^Suc i) g t) (at t)`)
      rather than `C_k_on`. That form is **self-propagating**: the chain for `Dh h f` on `Ush h U`
      follows from the chain for `f` on `U`, whereas re-establishing `C_k_on` for `Dh h f` would
      require transporting every continuity obligation, none of which the argument ever uses.
      `C_k_on` callers enter via `Ck_on_derivative_chain`.
- [x] A5. `Dh_iterate_error_all` (the induction, with `f`/`U`/`x`/`M` carried by explicit `\<forall>`) and
      its `C_k_on` corollary `Dh_iterate_error`:
      `\<bar>(Dh h ^^ j) f x - (deriv^^j) f x\<bar> \<le> real j * M * h`
- [x] A6. `forward_diff_eq_Dh` (the uniform-partition bridge) and **`forward_diff_consistency`**,
      which is (4.4) in the paper's own notation:
      `\<bar>forward_diff f xs h j k - (deriv^^j) f (xs!k)\<bar> \<le> real j * M * h`
      for `M` bounding `\<bar>(deriv^^Suc j) f\<bar>` on `[xs!k, xs!(k+j)]`, i.e. the paper's `C\<twiddle>\<^sub>j = j\<sqdot>M`,
      depending only on `f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)` exactly as claimed.
- [x] A7. `forward_diff_{one,two,three,four}_error_bound` left in place, NOT deleted: their ad-hoc
      constants (`M/2` for `j=1`) are sharper than the general `j\<sqdot>M`, and
      `Simultaneous_Approximation.thy` cites the `j=1` one.

**Relation to the pre-existing `forward_diff_recursive`** (`Derivative_Approximation.thy:211`):
that lemma is the same Pascal computation in *index* form,
`\<Delta>\<^sup>j\<^sup>+\<^sup>1\<^sub>k f = (\<Delta>\<^sup>j\<^sub>k\<^sub>+\<^sub>1 f - \<Delta>\<^sup>j\<^sub>k f)/h`, tied to the partition list `xs`. It is not a substitute for
`Dh_iterate_sum`: the induction here has to apply its hypothesis to the *function* `D\<^sub>h f`, which
the `xs`-indexed form cannot name. The two are complementary, not duplicates.

**Why the obvious induction fails** (worth not re-deriving): comparing `E\<^sub>j\<^sub>+\<^sub>1` to `E\<^sub>j` directly
produces the term `(E\<^sub>j(x+h) - E\<^sub>j(x))/h`, whose bound does **not** shrink with `h` — the `1/h`
cancels the gain. The induction hypothesis must be applied to `D\<^sub>h f`, not to `f`, and that is
what forces the commutation lemma A2. Likewise the "mean value theorem for finite differences"
route (`(D\<^sub>h\<^sup>j f)(x) = f\<^sup>(\<^sup>j\<^sup>)(\<xi>)` for some `\<xi>`) does not induct: the two MVT points from the
hypothesis are `h`-apart in the wrong ratio.

### Gotchas hit while proving Gap 1

- **`eval_at` exits 0 even when the theory fails, and the FIRST error aborts the run.** An error
  at line 7 masked everything after it and briefly read as a clean run. Only
  `grep "Error at line"` over the *whole* output is a real signal; never trust the exit code or a
  clean tail.
- A doc antiquotation `\<^const>\<open>Dh\<close>` in the theory header, *before* the definition, is a hard error.
- `simp add: sum.atLeast0_atMost_Suc_shift` does not fire: the top-split rule
  `sum.atLeast0_atMost_Suc` also applies and `simp` picks it. Use `subst` to force the intended
  split.
- `simp` **cancels a common factor out of a rewrite rule you supply**, turning
  `real (j choose v) * ... = real (j choose v) * P v` into a conditional rule
  (`j < v \<or> ...`) that then no longer matches under a `sum` binder. Rewrite sums with an explicit
  `sum.cong[OF refl]`, never by feeding simp a pointwise `\<And>v` equation.
- `simp` normalises `f ^^ Suc j` to `f \<circ> (f ^^ j)`, so the residual goal after it wants
  `funpow_swap1`, not `funpow_Suc_right`.
- `mult_mono`'s third subgoal is `0 \<le> b` (the larger *left* factor), not `0 \<le> d`.
- `blast` will not use `\<forall>x. lhs = rhs` to close a goal stated `rhs = lhs`; state the natural
  orientation and `rule sym`.
- **Two more `document = pdf` traps, both invisible to every proof check** (the same class as the
  `H\<ouml>lder` regression recorded in `THEOREM_3_2_PLAN.md`): `\<twiddle>` has no LaTeX definition
  (write `Ctilde\<^sub>j`, not `C\<twiddle>\<^sub>j`), and `\<dots>` breaks in *prose* inside a `text` block, though it
  is fine inside `\<open>\<dots>\<close>`. Both only surface in the full `isabelle build`, never in `eval_at`,
  so a green `eval_at` is not evidence the session builds. `\<sqdot>` and `\<parallel>` are fine.

---

## Gap 2: Theorem 4.2 — the quantitative rate

Not stated anywhere. The `\<eta>`-bounds inside `Simultaneous_Approximation.thy`'s `J\<^sub>1`/`I\<^sub>1` chain
already have the right asymptotic shape but were never packaged into a closed-form constant.

**Do `j=1` first.** This mirrors 5.1 \<rightarrow> 5.2 exactly: the existing `j=1` machinery bounds
coefficient differences crudely because it picks its `\<sigma>`-saturation tolerance *after* `N`; the
quantitative version must thread an explicit `C\<twiddle>\<^sub>1`/`L\<^sub>1` through instead. The 5.2 work solved
precisely this by adding a `Df` parameter to the existing bound lemmas and recovering the old
statement by instantiating it — **the same in-place-generalization trick should apply here**, and
it kept Theorem 5.1 completely unaffected.

### Checklist — **GAP 2 CLOSED at `j=1` 2026-09-04**, all verified, capstone green

New file `Simultaneous_Approximation_Rate.thy` (imports `Simultaneous_Approximation` +
`Forward_Difference_Consistency`), ~615 lines. **No existing file was edited.**

- [x] B1. No new predicate needed: `deriv_lipschitz_bound` (`Derivative_Approximation.thy:69`)
      already gives `\<bar>f'(x)-f'(y)\<bar> \<le> C\<^sub>1\<sqdot>\<bar>x-y\<bar>` with `C\<^sub>1 = Sup\<bar>f''\<bar>` on `[a,b]`, so `L\<^sub>1 = C\<^sub>1`.
      Helper `C1_sup_nonneg` extracted (`0 \<le> C\<^sub>1`, needed everywhere).
- [x] B2. `forward_diff_one_J1_rate_bound` — the `1/N`-explicit counterpart of
      `forward_diff_one_J1_eta_bound`, concluding `\<le> (1/N)(2C\<^sub>1(b-a) + M\<^sub>1)`. **This matches the
      paper's own `J\<^sub>1` constant exactly**: with `Ctilde\<^sub>1 = C\<^sub>1/2` and `L\<^sub>1 = C\<^sub>1`, the paper's
      `2Ctilde\<^sub>1(b-a) + L\<^sub>1(b-a) + \<parallel>f'\<parallel>\<^sub>\<infinity>` is exactly `2C\<^sub>1(b-a) + M\<^sub>1`. The paper's silently-absorbed
      `O(1/N\<^sup>2)` fourth term is absorbed explicitly here, into the slack from the sums running
      over `M < N` terms rather than `N`.
- [x] B3. `deriv_lipschitz_delta_prop` plus `forward_diff_one_{generic,left_boundary,
      right_boundary}_L_rate_bound` — the three `J\<^sub>2` bounds at the mesh scale, via `\<delta> := 3h`,
      `\<eta> := 3(C\<^sub>1+1)h`. (The `+1` is what keeps `\<delta>_prop`'s inequality strict when `C\<^sub>1 = 0`, i.e.
      `f'` constant; it costs an additive `3h` and preserves the `O(1/N)` rate.)
- [x] B4. **`forward_diff_one_rate`** — Theorem 4.2 at `j=1`:
      ```
      \<lbrakk>sigmoidal \<sigma>; bounded_function \<sigma>; a < b; N > 3; C_k_on 2 f U; {a..b} \<subseteq> U\<rbrakk> \<Longrightarrow>
        \<exists>w\<^sub>0>0. \<forall>w \<ge> w\<^sub>0. \<forall>x\<in>{a..b}.
          \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N 1 w x - deriv f x\<bar>
            < ((3\<sqdot>Sup\<bar>f''\<bar>\<sqdot>(b-a) + 2) \<sqdot> (4 + Sup\<bar>f'\<bar> + 4\<sqdot>Sup\<bar>\<sigma>\<bar>)) / N
      ```
      Note the quantifier order is 4.2's, not 4.1's: `N` is given, `w\<^sub>0` depends on it.
      `sigma_saturation_for_N` splits the `\<epsilon>`-independent part of
      `forward_diff_one_approximation_preamble` out to make that possible.
- [ ] B5. generalize to arbitrary `j` (depends on Gap 3's machinery)

### The key structural find

**The whole assembly is Theorem 4.1's case dispatch with `\<eta> := \<eta>\<^sub>N` and `\<delta> := 3h`, where**
```
\<eta>\<^sub>N := (3\<sqdot>C\<^sub>1\<sqdot>(b-a) + 2) / N
```
The existing `j=1` development constrains its abstract `\<eta>` by exactly three inequalities --
`hC\<^sub>1 < \<eta>`, `1/N < \<eta>`, and `\<eta>` being a modulus of continuity for `f'` at some `\<delta> > 2h` -- and
`\<eta>\<^sub>N` satisfies all three at once while being itself `O(1/N)` (`eta_N_facts`). So the three large
`*_I1_*_eta_bound` proofs (~800 lines between them) are **instantiated, not re-derived**, and
their final collapse `I\<^sub>1+J\<^sub>2 < \<eta>(4+M\<^sub>1+4S)` becomes the explicit rate directly. This was the
single highest-leverage observation in Gap 2; without it the estimate would have had to be
rebuilt from `forward_diff_one_J1_sum_bound` upward.

### Two deliberate divergences from the paper, both safe

1. The paper requires `N > j+3 = 4`; this needs only `N > 3`, inherited from Theorem 4.1.
2. The constant is `(3C\<^sub>1(b-a)+2)(4+M\<^sub>1+4S)` rather than the paper's
   `L\<^sub>1(b-a)(2S+3) + Ctilde\<^sub>1(b-a)(4S+3) + M\<^sub>1`. Both are `O(1)`, so the `O(1/N)` rate -- the
   theorem's actual content -- is identical. Same phenomenon already recorded for Theorem 5.2.
   The per-piece lemmas B2/B3 do record the paper's own constants (B2 matches exactly), so the
   comparison is available; a version with the paper's literal constant would combine B2 and B3
   instead of using `\<eta>\<^sub>N` uniformly, at the cost of re-deriving the `I\<^sub>1` layer.

### Gotchas hit while proving Gap 2

- `simp` will not get `0 < 3\<sqdot>C\<^sub>1\<sqdot>(b-a) + 2` from `0 \<le> C\<^sub>1` and `a < b`; the product positivity
  needs an explicit `mult_nonneg_nonneg`. Establish it once and reuse.
- **`unfolding` rewrites the goal, never the `using` facts.** `using goal unfolding foo_def .`
  silently leaves the two sides unable to meet when the definitions live on the fact side; use
  `goal[unfolded foo_def]` instead. Cost one round.
- `\<oline>` was replaced by `\<^sub>0` preemptively: it appears in no already-green file, exactly
  like `\<twiddle>`, which did break the document build. **Check any unusual `\<\<dots>>` symbol against the
  green files before using it in a comment.**

---

## Gap 3: Theorem 4.1 for general `j` — the big one

`Simultaneous_Approximation.thy` is 2,357 lines for `j=1` alone. General `j` needs:

1. The **four**-case `L\<^sub>i` split (`i=1,2` / `i=3,\<dots>,N-j` / `i=N-j+1` / `i=N-j+2,\<dots>,N`) rather than
   the three cases the `j=1` development uses. The extra case is the right-boundary truncation
   `i = N-j+1`, which is degenerate at `j=1` and so never appeared.
2. `N > j+3` rather than `N > 3`, and mesh condition `h < \<delta>/max{2,j}` rather than `h < \<delta>/2` —
   the `max{2,j}` is exactly what the `j=1` development dropped.
3. **The simultaneity quantifier**: one `N`, one `w`, all `j = 1,\<dots>,n`. The `\<sigma>`-saturation
   witness `w\<oline>(1/N)` from Lemma 2.1 does not depend on `j`, so this should come out of taking a
   max over the finitely many `j`, but it must be arranged deliberately — proving each `j`
   separately does **not** give the theorem as stated.

**Effort: comparable to redoing `Simultaneous_Approximation.thy`.** This is the one piece where
"just generalize the existing proof" is likely to be the wrong instinct; a fresh `j`-generic
development reusing `Partition_Facts.thy` is probably cheaper than retrofitting.

Knock-on: once done, Cor 6.1(ii)/6.2(ii) generalize to all `j \<le> n` by direct instantiation, the
way they already do at `j=1`.

### Progress: the node-level layer is DONE (2026-09-04), all verified, capstone green

New file `Simultaneous_Approximation_General_j.thy` (imports `Forward_Difference_Consistency`).
The `j=1` development rests on exactly three node-level facts, each originally derived from a
bespoke `j=1` Taylor expansion. With Gap 1's `forward_diff_consistency` in hand, all three
generalise, with `C\<^sub>1 = Sup\<bar>f''\<bar>` replaced by `L\<^sub>j = Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>` throughout:

- [x] `deriv_Sucj_bdd_above` / `deriv_Sucj_le_Sup` — `Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar>` on `[a,b]` is a genuine bound
      (continuity from `C_k_on (Suc j)`'s own `n=j` clause, then compactness). The `j=1`
      development re-derives this inline at each of `j=1,2,3,4`; now done once.
- [x] `Ck_on_open` — `C_k_on (Suc j) f U \<Longrightarrow> open U`, so `open U` never needs to be a hypothesis.
- [x] **`nth_deriv_lipschitz_bound`** — the general-`j` `deriv_lipschitz_bound`:
      `\<bar>f\<^sup>(\<^sup>j\<^sup>)(x) - f\<^sup>(\<^sup>j\<^sup>)(y)\<bar> \<le> Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar> \<sqdot> \<bar>x-y\<bar>`. **This is Theorem 4.2's `L\<^sub>j`**, so B5 now has its
      constant.
- [x] **`forward_diff_node_error`** — (4.4) at a partition node:
      `\<bar>\<Delta>\<^sup>j\<^sub>m f - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>m)\<bar> \<le> j \<sqdot> Sup\<bar>f\<^sup>(\<^sup>j\<^sup>+\<^sup>1\<^sup>)\<bar> \<sqdot> h` for `m \<ge> 1`, `m+j \<le> N+1`. (The `m \<ge> 1` is the real
      content of the left constraint: this project's indexing puts `xs!0 = a-h` *outside* `[a,b]`.)
- [x] `nth_deriv_node_diff_bound` — `\<bar>f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k) - f\<^sup>(\<^sup>j\<^sup>)(x\<^sub>k\<^sub>-\<^sub>1)\<bar> \<le> L\<^sub>j h`.
- [x] `forward_diff_coefficient_error` — a `G\<^sup>j\<^sub>N f` coefficient vs the corresponding
      `f\<^sup>(\<^sup>j\<^sup>)`-coefficient, `\<le> 2(j \<sqdot> L\<^sub>j \<sqdot> h)`.

### Progress: the `L\<^sub>i` case split (`J\<^sub>2` side) is DONE (2026-09-04), all verified, capstone green

All four of the paper's `L\<^sub>i` cases, at general `j`, in the same file. Translated into this
project's indexing (`xs!0 = x\<^sub>-\<^sub>1`, so paper index `k` is `k+1` here) and with the telescoping sums
`\<Sum>\<^sub>k\<^sub>=\<^sub>1\<^sup>m(\<Delta>\<^sup>j\<^sub>k f - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1 f) + \<Delta>\<^sup>j\<^sub>0 f = \<Delta>\<^sup>j\<^sub>m f` already collapsed:

- [x] Case 1 (`i \<in> {1,2}`) — `forward_diff_left_L_bound_gen`, bound `L\<^sub>j h (2(2j+1)S + j + 2)`
- [x] Case 2 (`i \<in> {3..N-j}`) — `forward_diff_generic_L_bound_gen`, same bound
- [x] Case 3 (`i = N-j+1`) — `forward_diff_right_L_bound_gen`, bound `L\<^sub>j h ((2j+1)S + j + 2)`
      (one `\<sigma>`-term instead of two)
- [x] Case 4 (`i \<in> {N-j+2..N}`) — `forward_diff_plateau_L_bound_gen`, bound `2 j L\<^sub>j h`
      (no `\<sigma>`-term at all)
- [x] helpers `sigma_abs_le_Sup`, `Lj_nonneg`

**Case 4 is empty when `j = 1`** (its range is `{N+1..N}`) — that is exactly why the existing
`j=1` development has only three cases and no analogue of it. Cases 1, 2, 3 have the same shapes
as its left-boundary, generic and right-boundary lemmas.

These are derived **directly** from (4.4) and the Lipschitz constant, not through an abstract
modulus-of-continuity pair `(\<delta>,\<eta>)` as the `j=1` lemmas are. That is both necessary (there is no
`j`-generic `\<eta>` layer to instantiate) and **sharper**: at `j=1` Case 2 gives `L\<^sub>1h(6S+3)` where
routing through `\<eta>` gives `L\<^sub>1h(8S+3.5) + 3h(1+2S)`.

### Progress: the `I\<^sub>1` side is DONE for the generic case (2026-09-04), verified, capstone green

- [x] `forward_diff_I1_generic_decomp_gen` — the reindex + telescope identity. Reindexing (4.3)'s
      sum `k \<in> {1..N-j}` by `m = k+1` puts `G\<^sup>j\<^sub>N f` in the shape
      `\<Sum>\<^sub>m\<^sub>\<in>\<^sub>{\<^sub>2\<^sub>.\<^sub>.\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1\<^sub>}(\<Delta>\<^sup>j\<^sub>m-\<Delta>\<^sup>j\<^sub>m\<^sub>-\<^sub>1)\<sigma>\<^sub>m + \<Delta>\<^sup>j\<^sub>1\<sigma>\<^sub>0`; `L\<^sub>i`'s leading `\<Delta>\<^sup>j\<^sub>i\<^sub>-\<^sub>1` telescopes into the initial
      segment and its two `\<sigma>`-terms cancel the `m = i, i+1` terms exactly. **Only the upper
      summation limit differs from `j=1`: `N-j+1` for `N`.** This layer is purely algebraic and
      is stated with *no* hypotheses about `f`, `\<sigma>` or the partition.
- [x] `node_gap_general` — node gaps at **every** index including `0` and in either order.
      `difference_of_terms` covers only `{1..N+1}` and only increasing order, but the `\<Delta>\<^sup>j\<^sub>1\<sigma>\<^sub>0`
      term needs `xs!0 = a-h` and the right-hand sum needs decreasing gaps.
- [x] `deriv_j_bdd_above` / `deriv_j_le_Sup` — `Sup\<bar>f\<^sup>(\<^sup>j\<^sup>)\<bar>` is a genuine bound (`C_k_on (Suc j)`
      makes `f\<^sup>(\<^sup>j\<^sup>)` differentiable, hence continuous).
- [x] `forward_diff_adjacent_bound_gen` — the uniform per-term bound
      `\<bar>\<Delta>\<^sup>j\<^sub>k - \<Delta>\<^sup>j\<^sub>k\<^sub>-\<^sub>1\<bar> \<le> (2j+1)L\<^sub>jh` for every `k \<in> {2..N-j+1}`, wherever `k` sits relative to the
      active cell.
- [x] `forward_diff_one_term_bound_gen` — `\<bar>\<Delta>\<^sup>j\<^sub>1\<bar> \<le> jL\<^sub>jh + M\<^sub>j`.
- [x] `sat_gap_left` / `sat_gap_right` — the geometry that feeds `\<sigma>`-saturation: nodes left of the
      cell are `\<ge> h` left of `x`, nodes two or more steps right are `\<ge> h` right.
- [x] **`forward_diff_I1_generic_rate_gen`** —
      `I\<^sub>1 \<le> ((2j+1)L\<^sub>j(b-a) + (jL\<^sub>jh + M\<^sub>j)) / N`.
- [x] **`forward_diff_generic_rate_gen`** — the two halves joined:
      ```
      \<bar>G\<^sup>j\<^sub>N f(x) - f\<^sup>(\<^sup>j\<^sup>)(x)\<bar>
        \<le> ((2j+1)L\<^sub>j(b-a) + jL\<^sub>jh + M\<^sub>j + L\<^sub>j(b-a)(2(2j+1)S + j + 2)) / N
      ```
      for `i \<in> {3..N-j}` — an explicit `O(1/N)` bound at general `j`, i.e. Theorem 4.2's assertion
      for the paper's Case 2 (which is where the paper confines its own `J\<^sub>1` estimate).

### Progress: ALL FOUR cases now complete end-to-end (2026-09-04), verified, capstone green

- [x] `forward_diff_I1_tail_decomp_gen` — **Cases 3 and 4 in one lemma**, parametrised by the cut
      point `p` where `L\<^sub>i`'s leading `\<Delta>\<^sup>j` sits. `p = N-j` is Case 3 (trailing sum = the single
      term `m = N-j+1`, i.e. its one `\<sigma>`-term); `p = N-j+1` is Case 4 (trailing sum empty,
      matching `L\<^sub>i = \<Delta>\<^sup>j\<^sub>N\<^sub>-\<^sub>j\<^sub>+\<^sub>1` with no `\<sigma>`-term). Neither has a node to the *right* of the active
      cell, so both remainders carry only a left sum. Stated as an **equation** — the
      cancellation is exact; the absolute value is cleaner applied afterwards.
- [x] `forward_diff_I1_head_decomp_gen` — Case 1, the mirror image: no left sum, right sum starts
      at `m = 4` because `L\<^sub>i`'s two `\<sigma>`-terms cancel the `m = 2,3` terms.
- [x] `forward_diff_I1_tail_rate_gen` — Cases 3/4 at rate `\<le> ((2j+1)L\<^sub>j(b-a) + (jL\<^sub>jh + M\<^sub>j))/N`.
      Its only geometric input is an anchor `x\<^sub>q \<le> x` with `p+1 \<le> q`, so one lemma serves both
      (Case 3: `q = N-j+1`; Case 4: `q = i \<ge> N-j+2`).
- [x] `forward_diff_I1_head_rate_gen` — Case 1, same bound.
- [x] `forward_diff_{left,right,plateau}_rate_gen` — the three remaining joins. Together with
      `forward_diff_generic_rate_gen` this gives an explicit `O(1/N)` bound at general `j` for
      **every** `x \<in> [a,b]`, whichever of the four cases its cell falls in:
      | case | `i` range | bound numerator over `N` |
      |---|---|---|
      | 1 | `{1,2}` | `(2j+1)L\<^sub>j(b-a) + jL\<^sub>jh + M\<^sub>j + L\<^sub>j(b-a)(2(2j+1)S+j+2)` |
      | 2 | `{3..N-j}` | same |
      | 3 | `N-j+1` | `\<dots> + L\<^sub>j(b-a)((2j+1)S+j+2)` |
      | 4 | `{N-j+2..N}` | `\<dots> + 2jL\<^sub>j(b-a)` |

### GAP 3 CLOSED (2026-09-05), and B5 with it

- [x] `forward_diff_rate_gen` — the case dispatch. `exists_containing_interval` locates the cell;
      the four ranges exhaust `{1..N}` given `N > j+3` and `j \<ge> 1`.
      **The four constants are not comparable pairwise**: Case 4's `2jL\<^sub>j(b-a)` is *not* dominated
      by Case 1/2's `L\<^sub>j(b-a)(2(2j+1)S+j+2)` when `\<sigma>` is small and `j` large (at `S = 0` that would
      need `j \<le> 2`). The uniform statement therefore uses `2(2j+1)S + 2j + 2`, which dominates all
      four.
- [x] **`forward_diff_rate`** — Theorem 4.2 at general `j`, packaging the dispatch with
      `sigma_saturation_for_N`.
- [x] **`forward_diff_simultaneous_approximation`** — **Theorem 4.1 at general `j`**, the real
      goal:
      ```
      \<lbrakk>sigmoidal \<sigma>; bounded_function \<sigma>; a < b; C_k_on (Suc n) f U; {a..b} \<subseteq> U; 1 \<le> n; 0 < \<epsilon>\<rbrakk> \<Longrightarrow>
        \<exists>N w. n + 3 < N \<and> 0 < w \<and>
          (\<forall>j\<in>{1..n}. \<forall>x\<in>{a..b}.
             \<bar>Gj_network \<sigma> f (unif_part a b N) ((b-a)/N) N j w x - (deriv^^j) f x\<bar> < \<epsilon>)
      ```
      plus the helper `C_k_on_mono` (`C_k_on` is antitone in its order, for nonzero orders).
      **The simultaneity turns on one fact**: `w\<^sub>0` comes from `sigma_saturation_for_N`, which
      depends on `N` and `h` but **not on `j`**. So one `w\<^sub>0` serves every `j` once `N` is fixed,
      and only `N` faces `j`-dependent constraints — finitely many, settled by
      `K = Max (Kf ` {1..n})` and `reals_Archimedean2`. Assembling from `n` separate applications
      of `forward_diff_rate` would give unrelated `N\<^sub>j`, `w\<^sub>j` and would **not** prove this theorem.

### Further gotchas from the close-out

- **`intro ballI` strips nested `\<forall>`s too.** On `\<forall>j\<in>A. \<forall>x\<in>B. P` it strips *both*, so `fix j x`
  and `assume` both must come at once. Exactly the trap already recorded for Theorem 5.2's
  `intro exI \<dots> allI impI`; the symptom is a `show` that "fails to refine any pending goal" with
  the bound variable shown schematic (`?j2`).
- **`define` folds the goal but leaves `?thesis` bound to the *unfolded* statement**, so a later
  `finally show ?thesis` no longer matches. Use `let ?x = \<dots>` (purely syntactic) when the
  abbreviation is only for readability, and reserve `define` for when you need the equation.
  Where a `define`d abbreviation must meet a goal stated without it, convert on the *fact* side
  with `main[unfolded x_def]` — `unfolding` only ever rewrites the goal.
- `rule` will not unify a numeral (`3`) against a pattern (`?i + 1`); instantiate first
  (`sat_gap_right[\<dots>, where i = 2]`) and let the numerals normalise.
- `mult_left_mono` takes its premises as `b \<le> c` then `0 \<le> a`; no `[rotated]` needed.
- Chained `\<le>`/`<` reasoning across a division is more robust as explicit `divide_right_mono` +
  `order_trans`/`linarith` than as `simp add: divide_right_mono`, which normalises the two sides
  differently (e.g. `2*(2*real j+1)` to `4*real j+2`) and then cannot match them.

Two notes retained for context:

- The **simultaneity quantifier is easier than it looks.** The `w` comes from
  `sigmoidal_uniform_approximation` at tolerance `1/N` and step `h` and does **not** depend on
  `j` at all (see `sigma_saturation_for_N`, `Simultaneous_Approximation_Rate.thy`). So one `w`
  serves every `j` automatically once `N` is fixed, and only `N` has to satisfy finitely many
  `j`-dependent constraints — a max over `j = 1..n`. What does *not* work is deriving the
  theorem from `n` separate per-`j` theorems, since those give unrelated `N\<^sub>j`, `w\<^sub>j`.
- The `\<eta>\<^sub>N` instantiation trick from Gap 2 should transfer verbatim to B5 once the general-`j`
  `*_eta_bound` layer exists, since the three constraints it satisfies are not `j`-specific.

### Gotchas hit here

- `simp add: abs_mult abs_minus_commute` cannot close `\<bar>A - B\<bar> = \<bar>v-u\<bar>\<sqdot>\<bar>D\<bar>` from `B - A = (v-u)D`:
  `abs_minus_commute` lets it oscillate between the two orientations and it settles on neither.
  Flip the equation explicitly first (`algebra_simps`), then `rule abs_mult`.
- **Never leave a multi-term triangle inequality to `simp add: algebra_simps`.** It distributes
  `(A-B)\<sqdot>\<sigma>` into `A\<sigma>-B\<sigma>` on *both* sides, after which the per-term bounds no longer match the
  goal's grouping. Chain `abs_triangle_ineq` by hand into `\<bar>t\<^sub>1+t\<^sub>2\<bar>`, `\<bar>t\<^sub>1+t\<^sub>2+t\<^sub>3\<bar>`, \<dots> and finish
  with `linarith`, which treats each `\<bar>\<dots>\<bar>` as an atom. (Whether `simp` happens to succeed depends
  on how the indices normalise: the same three-term step closed by `simp` in Case 2 and failed in
  Case 3.)
- `difference_of_terms` is stated as a `\<forall>`-implication, so `auto`/`blast` will **not** instantiate
  it from surrounding range facts. Name both indices explicitly:
  `difference_of_terms[OF h_def xs_def, of <lo> <hi>]`.
- `i + 1 \<in> {2..N}` needs the *lower* bound on `i` too; supplying only `i + 1 \<le> N` leaves
  `Suc 0 \<le> i` open.

---

## Recommended order

1. **Gap 1** (A1–A5). Self-contained, supersedes four ad-hoc lemmas with one theorem, unblocks
   everything else, and is the piece the paper itself leaves unproved.
2. **Gap 2 at `j=1`** (B1–B4). Known playbook from 5.2.
3. **Gap 3**, then B5.

## Standing rules (inherited from `THEOREM_3_2_PLAN.md`)

- Verify every lemma with `isabelle eval_at` before checking its box. Never assume a fix works.
- Build:
  ```
  isabelle build -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys/Smooth_Manifolds \
    -d "/home/dusty/Desktop/Real and Complex Analytic" \
    -d /home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation \
    -v Sigmoid_Universal_Approximation
  ```
- The user co-edits these files live in jEdit: re-read before editing, never clobber, no
  concurrent builds.
- Always give a `fixes` clause; never rely on a bare `lemma` generalizing free variables (the
  name `h` demonstrably does not generalize in this project — see the `Lp_norm_eq_seminorm`
  defect).
- No `H\<ouml>lder` in comments — it breaks `document = pdf`. Write `Hoelder`.
