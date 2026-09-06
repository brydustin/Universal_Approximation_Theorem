# Costarelli–Spigler fidelity and proof audit

> **Snapshot.** This records the findings as of 2026-09-05 and is not updated. File and line references below point at theories that have since been renamed or removed: `Lp_Mollifiers.thy` is now `Lp_Density.thy` (its unused 1-d mollifier block deleted), and the `(real,'n) vec` mollifier development it referred to has been deleted entirely. See [PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) for the current layout.


Audit date: 2026-09-05. Project: `Sigmoid_Universal_Approximation`.

**Historical snapshot:** this report describes the pre-repair sources verified at 12:55 CDT. Subsequent repairs and the verified counterexample to the printed Theorem 5.2 are recorded in [PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) and [PAPER_FIXES_TODO.md](PAPER_FIXES_TODO.md). Line references below are historical.

Reference: D. Costarelli and R. Spigler, *Constructive Approximation by Superposition of Sigmoidal Functions*, Analysis in Theory and Applications 29(2), 169–196 (2013), [publisher record and DOI](https://www.global-sci.com/index.php/ata/article/view/7982). The comparison uses the full local PDF, `../Costarelli-Spigler-ATA-2013-2.pdf`, including visual inspection of the printed formulas on pp. 185 and 190. Page numbers below are the journal's printed page numbers.

## Verdict

The current formalization contains substantial proved mathematics, but it should **not be described as a complete, statement-faithful formalization of the paper**. The principal problems are a different multivariate approximation operator, incomplete explicit-weight corollaries, and unexposed measure-theoretic restrictions. Matching the convergence order alone does not establish the paper's quantitative inequality.

This audit does not change any project theory or attempt to repair these discrepancies. It separates proof verification from correspondence with the paper.

## Proof verification

The audit snapshot contains all 20 current `.thy` files, including the capstone and its 19 direct imports. A source inventory counts 365 declarations beginning with `lemma`, `theorem`, or `corollary`; this is a declaration count, not the number of individual stored facts. Editor backups and old generated documents are not part of this session.

A separate session, `Sigmoid_Paper_Audit_20260905`, was created at `/tmp/sigmoid_paper_audit.MenznB`. It uses copies of the source files and the existing `Real_and_Complex_Analytic` parent, not the `Sigmoid_Universal_Approximation` heap or any of the project's partial dependency heaps. The session has `quick_and_dirty = false` and document generation disabled. The additional `Audit_Check.thy` traverses the stored project facts, checks transitive oracle dependencies and hidden theorem hypotheses, and reports fixed free term variables and project axioms/definitions.

Final verification: **PASS, exit code 0**, completed at 12:55:53 CDT on 2026-09-05, in 59 seconds overall. All 20 project theories were processed from source. The diagnostic reported:

```text
AUDIT: 402 project fact entries checked; no transitive oracle dependencies
AUDIT: no hidden theorem hypotheses
AUDIT: 0 fact entries with fixed free term variables
```

The reported project axioms were exclusively definitional equations (`*_def_raw`), consistent with the source inspection finding no ad hoc axiomatization or proof-bypass commands. The textual occurrence of `axiomatization` in `Lp_Approximation.thy:47` is explanatory prose about HOL's `undefined`, not a declaration. At the end of verification, all 20 live theory files were byte-for-byte identical to the audit copies.

The successful build database is `/home/dusty/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux/log/Sigmoid_Paper_Audit_20260905.db`; its session record has return code 0. The diagnostic messages were retrieved from its `Sigmoid_Paper_Audit_20260905.Audit_Check:PIDE/messages` export. Preliminary runs processed the project theories; their failures were in the audit harness (a missing copied documentation file and ML API/context handling), not project proof failures.

Reproduction command:

```bash
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build -v \
  -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys/Smooth_Manifolds \
  -d '/home/dusty/Desktop/Real and Complex Analytic' \
  -D /tmp/sigmoid_paper_audit.MenznB
```

The dependency session was also rebuilt successfully during preparation. This remains verification relative to Isabelle/HOL and the imported libraries; it is not a claim that HOL has no foundational axioms.

## Findings requiring attention

### 1. The multivariate network is not equation (5.1)

**High priority; affects the claimed correspondence for Theorems 5.1–5.4.**

The paper's coefficients in (5.1), pp. 182–183, are

`f(x_i,y_j) - f(x_i,y_(j-1))`, with boundary coefficient `f(x_i,y_0)`.

The radial centers, separately, are the midpoints `(t_xi,t_yj)`. The distinction between sampling points and radial centers matters.

In [Multivariate_Approximation.thy](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Multivariate_Approximation.thy:109), `grid_point` uses midpoints in every coordinate, except the distinguished coordinate at height zero. At line 299, `multivariate_network` uses these points **both for evaluating f in the coefficients and for radial centers** at positive heights. `sigma_anchor` correctly handles the exterior radial center for the height-zero term, but does not restore endpoint sampling of f.

This is a different operator, not merely the documented one-position shift in list indexing. A direct example makes the difference explicit: use `Q = [0,1]^2`, `N = 3`, `f(x,y) = x`, the Heaviside activation, and evaluate at `(1/6,0)` with the second coordinate distinguished. All vertical coefficient differences vanish and only the first column's boundary term survives. The paper's operator returns `1/3`; the project's operator returns `1/6` (for any positive weight). This example is a direct mathematical evaluation of the definitions, not an additional Isabelle lemma.

The proved midpoint variant is useful. However, its n-dimensional generality does not make it a stronger version of the paper's theorem about a different, fixed operator. To establish that correspondence, introduce the paper's endpoint sampling separately from the midpoint radial centers and prove the results for that operator. Preserve the current variant under an accurate name if desired.

### 2. Corollaries 6.1 and 6.2 are not fully formalized

**High priority; missing conclusions and prescribed parameter choices.**

On pp. 188 and 190, the paper specifies the weights explicitly and obtains one `N > n+3` that approximates f and all derivatives of orders `1..n`. The logistic weight is `N/(b-a) * ln(N-1) + delta`, for positive delta. The Gompertz corollary likewise uses its displayed logarithmic maximum and positive slack.

The project's [logistic_approximation_theorem](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Concrete_Sigmoidal_Examples.thy:32) and [gompertz_approximation_theorem](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Concrete_Sigmoidal_Examples.thy:419) existentially quantify both N and w. Their derivative counterparts at lines 53 and 438 cover only the first derivative, again with separately existential N and w. They do not identify the witnesses across f and its derivatives and do not fix the paper's weights.

`logistic_step_saturation` (line 138) and `gompertz_step_saturation` (line 380) provide important ingredients, but are not assembled into those corollaries. The general-j theorem elsewhere also supplies ingredients, rather than an already stated joint explicit-weight corollary. The Gompertz threshold in the formal lemma is a signed sufficient threshold with an explicit positive-weight assumption; the paper's maximum contains absolute values. This can be reconciled by an inequality, but that bridge and the final corollary are not present.

### 3. Theorems 3.2 and 5.4 assume globally Borel-measurable representatives

**Medium priority; a real restriction in the exported statements, usually repairable by a representative argument.**

Both [sigmoidal_Lp_approximation_theorem_general](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Lp_Approximation_General.thy:233) and [multivariate_sigmoidal_Lp_approximation_theorem_general](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Multivariate_Lp_Approximation_General.thy:26) assume `f ∈ borel_measurable borel` on the entire ambient space, in addition to integrability of `|f|^p` on the approximation domain.

The paper assumes membership in Lp of the bounded domain. This does not require the particular total function representing f to be Borel measurable everywhere, including outside that domain. Even within the domain, completed Lebesgue measurability is weaker than Borel measurability of that particular representative.

For the usual Lp space modulo almost-everywhere equality, a Borel representative and zero-extension argument should remove this gap. The current project does not expose that reduction as a final corollary. State the current results as results for Borel representatives until that bridge is proved. No continuity or boundedness assumption on f appears in these two final theorems.

### 4. All four Lp results add Borel measurability of sigma

**Explicit qualification required; not evidence of an illegitimate shortcut by itself.**

Theorems 3.1, 3.2, 5.3 and 5.4 in the paper say bounded sigmoidal. All four formal counterparts add `sigma ∈ borel_measurable borel`. Boundedness and the two limits alone do not imply measurability: arbitrary nonmeasurable behavior on a bounded interval is compatible with both limits.

Thus the additional premise is mathematically substantive and must be disclosed. It provides a sound sufficient condition for measurable networks and ordinary Lebesgue Lp errors. It is much weaker than the old continuity premise, and the verified Heaviside example at [Concrete_Sigmoidal_Examples.thy:506](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Concrete_Sigmoidal_Examples.thy:506) demonstrates that discontinuous activations are supported.

Do not simply remove this premise to imitate the paper: the interpretation of the paper's Lp expressions for arbitrary nonmeasurable activations first needs to be settled. This audit identifies the specification issue; it does not prove a counterexample to the paper's full existential Lp assertions. Borel measurability is sufficient, not asserted here to be the minimal possible condition.

### 5. The quantitative statements differ

**Medium priority for Theorem 4.2; high priority for a literal claim about Theorem 5.2.**

[forward_diff_rate](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Simultaneous_Approximation_General_j.thy:2092) proves the correct all-large-weights quantifier and an explicit O(1/N) estimate, for all `N > j+3`. Its coefficient differs from the printed Theorem 4.2 and includes a further O(1/N) term inside the numerator. It uses a pointwise `≤` bound rather than the printed strict supremum bound. This still establishes the advertised convergence order. Because the paper allows a derivative-dependent consistency constant, a larger choice of that constant may permit a paper-shaped corollary; that wrapper has not been formalized.

[multivariate_holder_rate](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Multivariate_Holder_Rate.thy:55) gives

`[1 + (1+S) L ((b-a)(d+2))^alpha] / N^alpha`,

where `S = sup |sigma|` and `d = CARD('n)`. The paper's printed coefficient on p. 185 is

`L 2^(alpha/2+1) (b-a)^alpha + 2^(alpha/2) (b-a)^alpha S + ||f||_infinity`.

The project explicitly acknowledges the changed constant in its theory text, and chooses a different saturation tolerance in its proof. In addition, it uses the changed operator from finding 1. Therefore this is an O(N^-alpha) theorem for the project's operator, not verification of the displayed inequality for (5.1). The printed formula's constants should be checked carefully when formalizing it, rather than assumed correct from the rate alone.

### 6. The mollifier construction for general Lp input is not the implemented proof route

**Proof-construction limitation; not an extra hidden assumption on the final density results.**

The proofs of Theorems 3.2 and 5.4 use `continuous_dense_Lp` ([Lp_Mollifiers.thy:1267](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Lp_Mollifiers.thy:1267)), obtained through simple functions and continuous approximations. They do not return the paper's specific convolution-based coefficients.

The existing [mollifier_convolution_Lp_convergence](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Mollifiers.thy:1609) assumes f globally bounded and continuous and proves convergence over a bounded set. That is substantially narrower than the general Lp mollifier convergence used on the zero-extension of arbitrary Lp data in the paper. These stronger hypotheses do not leak into the final Theorem 3.2/5.4 statements because those proofs take the density route instead.

The mollifiers use the library bump supported at radius 2, scaled to radius 2/k, rather than the particular radius-1 formula (3.3)–(3.4). This is a harmless choice for an approximate identity, but further distinguishes the development from a verification of the paper's explicit coefficient recipe. Generic existence in HOL should not be advertised as an extracted implementation of that recipe.

## Result-by-result correspondence

| Paper result | Formal result | Fidelity assessment |
|---|---|---|
| Definition 2.1 | `sigmoidal` | Matches the two limits; does not silently require monotonicity or continuity. |
| Lemma 2.1 | `sigmoidal_uniform_approximation` | Matches, including one threshold valid for every larger weight and every listed node. |
| Theorem 2.1 | `sigmoidal_approximation_theorem` | Matches the network and essential assumptions on a nondegenerate interval. List indices are shifted by one. |
| Theorem 3.1 | `sigmoidal_Lp_approximation_theorem` | Correct network; extra Borel measurability of sigma. |
| Theorem 3.2 | `sigmoidal_Lp_approximation_theorem_general` | Density conclusion for Borel representatives and measurable sigma; different construction of the continuous approximant. |
| Equations (4.2), (4.3) | `forward_diff`, `Gj_network` | Match after the explicit one-position index shift. Coefficients use values of f, not assumed derivative samples. |
| Estimate (4.4) | `forward_diff_consistency` | General-j O(h) consistency, with explicit constant `j*M` under the expected derivative bound. |
| Theorem 4.1 | `forward_diff_simultaneous_approximation` | Matches the displayed derivative-order quantifiers: one N and w for every j in `1..n`. |
| Theorem 4.2 | `forward_diff_rate` | Same operator, regularity and rate; different explicit bound and strictness presentation. |
| Lemma 5.1 | `sigmoidal_uniform_approximation_dist` | Faithful generalization to real normed vector spaces. |
| Theorem 5.1 | `multivariate_uniform_approximation` | Proves a modified midpoint-sampling operator in arbitrary finite dimension. |
| Theorem 5.2 | `multivariate_holder_rate` | Modified operator and different explicit constant, with the same asymptotic exponent. |
| Theorem 5.3 | `multivariate_sigmoidal_Lp_approximation_theorem` | Modified operator, extra measurable-sigma premise. |
| Theorem 5.4 | `multivariate_sigmoidal_Lp_approximation_theorem_general` | Modified operator, Borel target representatives, measurable sigma, density-based construction. |
| Corollary 6.1 | Two logistic approximation corollaries plus saturation lemmas | Missing prescribed-weight, common-N statement for f and all derivative orders. |
| Corollary 6.2 | Two Gompertz approximation corollaries plus saturation lemmas | Same missing assembly as Corollary 6.1. |

The derivative regularity assumption is **not** an unjustified analyticity assumption. `C_k_on` is defined in `Real and Complex Analytic/Limits_Higher_Order_Derivatives.thy:259` by differentiability and continuity of the derivative chain on an open set. `C_k_on (Suc n) f U` with `[a,b] ⊆ U` corresponds to the paper's explicitly defined smooth extension to a neighborhood of the closed interval (p. 170). Loading a library called `Real_and_Complex_Analytic` does not assume that f is analytic. Derivative bounds used by the final approximation theorems are derived on the compact interval, not assumed as an extra global bound.

Two minor presentation qualifications also apply. The multivariate domain is `[a,b]^d`, whereas the printed square allows independently translated coordinate intervals; a translation corollary would expose that routine reduction. Uniform existence statements use `∀x. |error x| < epsilon`; a strict supremum formulation follows by invoking them at epsilon/2. A pointwise strict bound at the same epsilon alone need not give a strict supremum bound when sigma is discontinuous.

The paper's Remark 4.1 analysis of differentiating the original network is not established as such by a named project result. The coordinate choice `r0` captures the idea of switching the distinguished axis in Remark 5.2, but does not fix the operator discrepancy. Section 6's arctangent example and Section 7's numerical experiments are not reproduced as formal results. There is a tanh/logistic identity in `Sigmoid_Definition.thy:191` and a verified Heaviside development. Additional logistic derivative identities, partition facts, integration inequalities and auxiliary results are project mathematics checked by the source build, not additional numbered Costarelli–Spigler theorems.

## Norm definitions and specification hygiene

The four public Lp results now use `Lp_enorm` ([Lp_Inequalities.thy:615](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Lp_Inequalities.thy:615)). The proofs establish the necessary integrability and use the bridge to the extended-valued expression. For example, the general univariate proof establishes `Gf_int_ab` at line 350 before its final conversion at line 377; the multivariate proof establishes `Gnf_int_Q` at line 224 before conversion at line 251. Thus the audited main results do not rely on the Bochner integral's zero default for nonintegrable functions.

However, the commentary about `undefined` enforcing obligations is too strong. `Lp_norm` returns an unspecified real outside its integrable domain, and `Lp_enorm` returns an unspecified extended real if `|g|^p` is not measurable. These are total HOL functions, not partial types or automatic proof-obligation mechanisms. For example, an unspecified real still has some positive upper bound. A bare `Lp_enorm ... < ennreal epsilon` should not generally be interpreted as a proof of measurability without the accompanying premises. The current main results supply suitable premises; future exported statements should also retain explicit domain conditions or use an API whose out-of-domain behavior enforces the intended property.

The opening claim in [SECTION_4_GAPS.md:3](/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/SECTION_4_GAPS.md:3), “Section 4 is complete, and with it the whole paper,” is not supported by this fidelity audit. The later description of Section 5 as simply stronger because of dimension also overlooks the changed operator. Those completion claims should be corrected when the project documentation is next updated.

## Recommended repair order

1. Introduce the exact operator (5.1), separating endpoint samples from midpoint radial centers, and prove its uniform and Lp results.
2. Assemble full Corollaries 6.1 and 6.2 with the displayed weights, one N, f, and every derivative order through n.
3. Add final Lp corollaries for arbitrary completed-Lebesgue representatives on the domain; keep the activation measurability qualification explicit.
4. Prove paper-shaped quantitative corollaries, checking constants and strict supremum bounds individually.
5. If claiming the paper's explicit constructive Lp recipe, complete general Lp mollifier convergence and return the corresponding coefficients.
6. Update completion claims and the discussion of norm guards to match the exported results.
