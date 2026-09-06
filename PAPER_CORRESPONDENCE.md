# Paper correspondence after the 2026-09-05 repairs

Reference: D. Costarelli and R. Spigler, *Constructive Approximation by Superposition of Sigmoidal Functions*, Analysis in Theory and Applications 29(2), 169–196 (2013), [publisher record](https://www.global-sci.com/index.php/ata/article/view/7982), DOI 10.4208/ata.2013.v29.n2.8. Printed page numbers are used below.

The original findings are preserved in [the audit snapshot](PAPER_AUDIT_2026-09-05.md). The current work list is [PAPER_FIXES_TODO.md](PAPER_FIXES_TODO.md). This document supersedes historical whole-paper completion claims, not the historical verification results.

## Current statement correspondence

| Paper | Current Isabelle result or definition | Correspondence and qualifications |
|---|---|---|
| Definition 2.1 | sigmoidal | The two limits only. Boundedness is the separate predicate bounded_function, matching the paper's "boundedness, continuity and/or monotonicity may be prescribed in addition"; continuity and monotonicity are never imposed. |
| Lemma 2.1 | sigmoidal_uniform_approximation | Uniform saturation of sigma away from the nodes, in both directions, for every node of a finite list. |
| Lemma 5.1 | sigmoidal_uniform_approximation_dist | The radial companion of Lemma 2.1, generalized from R^2 to an arbitrary real normed vector space. |
| Equation (2.2) | G_network | The endpoint-coefficient univariate network. The list has the exterior node at index 0, so paper indices are shifted by one. |
| Theorem 2.1 | sigmoidal_approximation_theorem; sigmoidal_uniform_approximation_sup | Continuous targets; the latter gives the literal strict supremum conclusion. The fixed-parameter estimate is exposed for the prescribed-weight corollaries. |
| Theorem 3.1 | sigmoidal_Lp_approximation_theorem | Continuous targets and the ordinary extended-real Lp error; Borel-measurable activation is explicit. |
| Equations (3.1)-(3.4); radial extension after Theorem 5.4 | zero_extension, mollifier_bump, mollifier, mollified_target | Exact exponential bump, dimension-dependent normalization, support radius 1/k, and the convolution of the original completed-Lebesgue zero extension. |
| Theorem 3.2 | mollifier_approximation; sigmoidal_Lp_approximation_lebesgue; sigmoidal_Lp_approximation_theorem_general | The explicit integral-coefficient network approximates every Lebesgue Lp target. No global Borel, boundedness, or continuity assumption on the target. The existential Lebesgue form and the printed Borel-target form are both derived from the constructive one by instantiating the mollifier index. |
| Equations (4.2), (4.3), estimate (4.4) | forward_diff, Gj_network, forward_diff_consistency | Finite differences of target samples, not derivatives of the activation. Supporting lemmas are labelled by the enclosing paper result. |
| Theorem 4.1 | forward_diff_simultaneous_approximation; forward_diff_simultaneous_approximation_sup | One N and weight work for derivative orders 1 through n. The second gives the printed strict supremum conclusion for an arbitrary bounded sigmoidal activation. |
| Theorem 4.2 | forward_diff_paper_rate | The paper's displayed quantitative shape and a strict supremum bound, with an explicit enlarged derivative-dependent consistency constant. The older rate lemmas remain supporting estimates, not claims of the identical printed constant. |
| Equation (5.1) | multivariate_network, sample_point, grid_point, sigma_anchor | Function coefficients now sample endpoints. Positive-height radial centers remain midpoints; the boundary radial center is exterior. These roles are no longer conflated. |
| Theorem 5.1 | multivariate_uniform_approximation_sup; translated_multivariate_uniform_approximation | Strict supremum approximation. The translation wrapper allows a separate coordinate origin in each equal-length interval, including the paper's square [a,b] × [c,d]. |
| Theorem 5.2 | multivariate_holder_rate_sup | A verified replacement bound for the correct operator, not the false printed coefficient. See the counterexample below. |
| Theorem 5.3 | multivariate_sigmoidal_Lp_approximation_theorem; translated_multivariate_Lp_approximation | Corrected endpoint operator on [a,b]^d; Borel-measurable activation. The translated-domain wrapper carries it to independently translated equal-length coordinate intervals. |
| Theorem 5.4 | multivariate_mollifier_approximation; multivariate_sigmoidal_Lp_approximation_lebesgue; multivariate_sigmoidal_Lp_approximation_theorem_general; translated_mollifier_approximation | Corrected endpoint operator, the exact radial mollifier and integral coefficients, and arbitrary Lebesgue Lp targets on [a,b]^d and on translated boxes. The existential Lebesgue form and the printed Borel-target form are both derived from the constructive one. |
| Corollary 6.1 | logistic_paper_joint_approximation | The prescribed logistic weight, arbitrary positive slack, one N > n+3, the function and all derivatives 1..n, strict supremum errors. |
| Corollary 6.2 | gompertz_paper_joint_approximation | The printed Gompertz weight, including both absolute-value bars, arbitrary positive slack, and the same joint conclusion. |
| Other Section 6 examples | Logistic, Gompertz, Heaviside and related function lemmas | Unnumbered supporting properties and supplementary identities are labelled as such, not assigned invented paper theorem numbers. |
| Remark 5.2 | multivariate_network, and every Section 5 theorem, at the two choices of r0 | The distinguished difference coordinate r0 is a parameter throughout. The paper's (5.1) and the transposed (5.3) of Remark 5.2 are the two instances at CARD('n) = 2; no separate development. |
| RBF commentary before Theorem 5.1, and Remark 5.1 | multivariate_network; sigmoidal_uniform_approximation_dist | Informal in the paper, so not labelled on any result. The activation is applied to a signed distance from a center, never to an affine functional, which is the structural reason Lemma 5.1 replaces Lemma 2.1. Recorded in the theory header. |
| Remarks 4.1 and 5.1 | not formalized | Prose commentary. Remark 4.1 explains why differentiating G_N f is the wrong route, which is why Theorem 4.1 uses forward differences of f instead. |
| Equation (7.1); Example 7.1 | example_f, example_f', example_71_uniform_approximation, example_71_joint_approximation | The target and the derivative printed on p.192, which is proved to be its derivative. Theorem 2.1 and Corollary 6.1 are instantiated at it. |
| Equation (7.2); Example 7.2 | example_g, example_g_L1, example_g_Lp_integrable, example_72_mollifier_approximation | The target, its membership in L^1(R) as asserted, and the constructive Theorem 3.2 instantiated at it — the network with mollifier-integral coefficients that the paper plots. |
| Example 7.3 | example_h, example_h_continuous, example_73_uniform_approximation | The bivariate target on the square, continuous everywhere, with Theorem 5.1 instantiated at it for either choice of the distinguished coordinate. |
| Section 7 figures and reported errors | Not formalized | Figures 4-12 are plots, and the relative errors (approximately 1.08e-1, 5.88e-2, 7.27e-2, 9.40e-2) and sup-norm estimates are numerical measurements stated with an approximation sign. Nothing claims them, nor the comparative remarks about them. |

## Theorem 5.2 has a false printed bound

This is not just a changed proof constant. The file [Paper_5_2_Counterexample.thy](Paper_5_2_Counterexample.thy) verifies the following counterexample to the printed formula on p. 185.

- Q = [0,1]^2, N = 3, alpha = 1, and f(x,y) = 10y. This target is continuous, has Hölder constant L = 10, and supremum norm 10.
- The activation is 0 for negative arguments, 1 for positive arguments, and 10 at zero. It is Borel measurable, bounded and sigmoidal, with supremum norm 10. These are allowed by the paper's stated hypotheses.
- At z = (1/6,1/6), every positive weight gives the exact equation (5.1) network value 100/3. The target value is 5/3, so the absolute error is 95/3.
- The printed bound specializes to (30 sqrt(2) + 10)/3, which is strictly smaller than 95/3.

The verified facts cover the activation hypotheses, target hypotheses, exact network evaluation and numerical inequality. The theorem paper_5_2_counterexample proves that no positive weight satisfies even the corresponding pointwise-for-all-points bound, hence no such weight satisfies the stronger strict supremum bound printed in the paper.

The apparent missing factor is L in the activation-norm term. This is a mathematical finding of this audit, not a claim of a published erratum. The project does not assume monotonicity or a unit-range activation to conceal this problem.

The verified strict-supremum replacement, valid in dimension d, is:

    [2 + (1 + ||sigma||_infinity) L ((b-a)(d+2))^alpha] / N^alpha.

This replacement is deliberately identified as a different, non-sharp constant. It is not presented as a proof of the false printed formula or as a proof that merely inserting L gives a sharp corrected theorem.

## Assumption and norm safeguards

The final Lp target assumptions are local to the completed Lebesgue measure on the approximation domain. Lp_borel_representative_on supplies a global Borel representative agreeing almost everywhere there; Lp_enorm_cong_AE transfers the approximation error back to the original target.

The activation measurability premise remains explicit. Boundedness and sigmoidal limits permit arbitrary nonmeasurable behavior on a bounded set, so they alone do not justify ordinary Lebesgue Lp expressions. This is a qualification of the paper's wording, not a replacement by the much stronger assumption of continuous activation.

Lp_enorm returns infinity when its powered absolute value is nonmeasurable, as well as for divergent measurable integrals. Lp_enorm_finite_integrable proves that a finite public error bound implies integrability. The internal real-valued Lp_norm and multivariate_Lp_norm are used only with integrability premises: their unspecified values do not constitute a domain guard. The misleading older explanations have been corrected.

C_k_on expresses finite differentiability and continuity on an open neighborhood containing the interval. It does not impose analyticity, despite the parent library session's name.

For Theorem 4.2, the chosen consistency constant is (2j+2) sup|f^(j+1)| + 1. It depends on the target and derivative order, not N or the activation. It dominates the previously proved j sup|f^(j+1)| consistency coefficient. The strict margin is retained before taking the supremum.

## Explicit general-Lp mollifier construction

The previously missing construction is implemented in [Mollifiers.thy](Mollifiers.thy) and [Mollifier_Networks.thy](Mollifier_Networks.thy). The exact seed is exp(1/(norm(x)^2 - 1)) inside the unit ball and zero outside. Its normalized dilates have integral one, are smooth to every order, are nonnegative, and vanish outside radius 1/k. These are not the older library-bump kernels of support radius 2/k.

mollified_target S f k is the integral over S of rho_k(x-y) f(y). mollified_target_zero_extension identifies it with the whole-space convolution in (3.2), or its multivariate counterpart after (5.4). The coefficient definitions use the original f, not an arbitrarily chosen continuous approximation or a separately specified Borel representative.

The proof establishes normalized convolution contraction, continuity for integrable targets, and Lp convergence for unbounded targets. mollified_target_Lp gives convergence on the approximation domain; mollified_target_global_Lp gives convergence to the original zero extension in the whole ambient space, together with integrability of every positive-index error. The intermediate L1 premise is derived from Lp integrability and bounded support, not imposed on the final target.

Continuous-function density is used internally to prove convergence of this specific approximate identity. It no longer replaces the final mollified target. The final theorems first choose a sufficiently large mollifier index k and then obtain N and w for the network applied to that same rho_k * f-tilde. They assert this for every sufficiently large k.

The univariate coefficients are the differences of convolution integrals displayed after (3.4), with the separate integral at a for the boundary coefficient. In the multivariate network they are the analogous differences at the endpoint sample points in (5.1). The source comments identify the one-index offset in the univariate list representation. The coefficient-integrability lemma and whole-space/single-integral identities explicitly check that these are meaningful integrals, including for unbounded targets.

## Domain formulations

Theorem 5.1 has an exported translated-domain wrapper. [Translated_Lp_Approximation.thy](Translated_Lp_Approximation.thy) now carries Theorems 5.3 and 5.4 across the same transport, in both their existential and their coefficient-explicit forms, and specializes them to the paper's square. Translation is a measure isomorphism of the completed Lebesgue measure, so the Lp error and the mollifier coefficients transport exactly.

This covers the domain shapes the paper uses. It is not a claim of literal coverage of every possible domain formulation.

## Theory layout

The Lp layer is arranged so that no theory sits off the path of a stated result:

- [Lp_Inequalities.thy](Lp_Inequalities.thy) — Lp_seminorm and Lp_enorm, Hölder, Minkowski, measurability of the Lp integrand, and affine invariance of the Bochner integral over lborel. Imports only HOL-Analysis.
- [Lp_Restriction.thy](Lp_Restriction.thy) — bridges between lborel, lebesgue and lebesgue_on S, zero extension, and almost-everywhere Borel representatives.
- [Lp_Density.thy](Lp_Density.thy) — inner regularity, tent functions, and density of continuous functions in Lp. No mollifier is used here.
- [Mollifiers.thy](Mollifiers.thy) — the paper's own mollifier, equation (3.3), over 'a::euclidean_space, and its approximate-identity convergence.
- [Mollifier_Networks.thy](Mollifier_Networks.thy) — the coefficient formulas following (3.4) and the constructive Theorems 3.2 and 5.4.
- [Lp_Representatives.thy](Lp_Representatives.thy) — the existential Lebesgue-target forms of those two theorems, derived from the constructive ones.
- [Lp_Approximation_General.thy](Lp_Approximation_General.thy), [Multivariate_Lp_Approximation_General.thy](Multivariate_Lp_Approximation_General.thy) — the printed Borel-target Theorems 3.2 and 5.4, derived in turn from those, since a Borel target is measurable for the completed Lebesgue measure on the domain.

## Constructivity

Every Lp theorem in the project now reaches its conclusion through the paper's own construction. The witness produced by each of the four Theorem 3.2 / 5.4 statements is the mollified target rho_k * f-tilde of (3.2)/(3.3)/(3.4), and the network is the integral-coefficient network, read back through mollifier_network_eq or its multivariate counterpart. No stated result depends on an existence-only choice of continuous approximant.

Density of continuous functions in Lp survives, and is necessary, but only as an ingredient inside the mollifier convergence proof (compact_continuous_dense in Mollifiers.thy), where it supplies compactly supported continuous comparison functions. It is not an alternative route to any theorem.

What remains existential is what is existential in the paper: N, the weight w, and the mollifier index k, the last as "for every sufficiently large k". The coefficients are explicit in every theorem — sample differences in Theorems 2.1, 3.1, 5.1 and 5.3, forward differences of f in Theorems 4.1 and 4.2, mollifier integrals in Theorems 3.2 and 5.4 — and Corollaries 6.1 and 6.2 additionally prescribe w.

This is constructivity in the paper's sense, that "a precise analytic form of the sums would be obtained" (p. 174). It is not a claim of executability: the development is classical HOL throughout, uses choice for almost-everywhere representatives, and generates no code.

The earlier duplicate mollifier developments — a (real,'n) vec construction and a separate plain-real copy of it — were unused by any stated result and have been removed; their four dimension-generic measure lemmas were moved into Lp_Inequalities.thy. The single remaining mollifier is the paper's.

## Source loading and repeatable checks

Run ./open_sources.sh to open every project theory. Its logic image is Real_and_Complex_Analytic and its included source session is Sigmoid_Universal_Approximation. Thus the parent libraries may be prebuilt, but all this project's theories are read and processed from source. Existing unrelated heaps are not deleted.

ROOT explicitly sets quick_and_dirty = false and includes Proof_Audit after the capstone. Proof_Audit rejects transitive oracle dependencies, hidden theorem hypotheses, fixed free term variables, and non-definitional project axioms. Short correspondence comments precede every lemma, theorem and corollary declaration.

Verification counts and the final build time are recorded in PAPER_FIXES_TODO.md after the final source build.
