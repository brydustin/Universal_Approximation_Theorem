# FAC review response — checklist

Decision: **major revision / reject-and-resubmit**, six months. Reviewer 1 major revision,
Reviewer 2 reject, Reviewer 3 reject and resubmit.

## The central fact to lead with

The reviewed artefact was the single-theory development now kept at
`legacy/Universal_Approximation.thy` — 1,377 lines, the sigmoid theory plus Theorem 2.1.
Reviewer 3 measured it: *"At 1350 lines of code, it is a small proof."* Reviewers 2 and 3
both reject on contribution size.

Since submission this has become a formalization of **all** of Costarelli–Spigler:
28 theories, 445 lemmas/theorems/corollaries, Theorems 2.1, 3.1, 3.2, 4.1, 4.2, 5.1, 5.3,
5.4, Corollaries 6.1–6.2 and Section 7's three examples — in all dimensions where the paper
proves only `d = 2` — plus:

- **a verified counterexample to the paper's printed Theorem 5.2** (`Theorem_5_2_Counterexample.thy`),
  with an explicitly different, non-sharp replacement bound;
- **a defect in the paper's hypotheses**: the L^p theorems need Borel measurability of the
  activation, which the paper never states, because "bounded sigmoidal" admits a
  nonmeasurable σ and then the L^p error denotes nothing;
- **the constructive networks the paper only gestures at**: coefficients as the explicit
  mollifier integrals of (3.4), not an existentially quantified continuous approximant.

That last item is the direct answer to the constructivity complaint that all three
reviewers raise. It did not exist at submission.

**Every reviewer's "contribution too modest" verdict was formed against an artefact that no
longer describes this work.** The revision is not a patch to the old paper; it is a
different paper about a much larger development.

---

## A. Already addressed since submission (verify, then cite)

- [x] **R2: `Nth_derivative` should be `(deriv ^^ n) f`.** Done — the abbreviation is gone
      from the development entirely; `(deriv ^^ n) f` is used throughout.
- [x] **R1/R2/R3: "constructive" is unearned.** The L^p theorems now produce an explicit
      network whose coefficients are the mollifier integrals following (3.4); density of
      continuous functions survives only as an ingredient inside the mollifier convergence
      proof, not as a route to any stated theorem.
- [x] **R1: code availability.** Now at
      `https://github.com/brydustin/Universal_Approximation_Theorem`.
- [x] **R3: "What is a Heaviside function?"** Now formalized in
      `Concrete_Sigmoidal_Examples.thy` as a bounded, measurable, *discontinuous* sigmoidal
      witness — it also demonstrates that the measurability hypothesis is weaker than
      continuity rather than a restatement of it.
- [x] **R3: work out examples.** Section 7's three examples are formalized in
      `Numerical_examples.thy`, each exhibited as an instance of the theorem the paper
      invokes for it.

## B. Isabelle tasks — reviewer claims that can be checked and fixed in the code

These are the items the reviewers made *checkable* assertions about. Each should be tested,
not assumed.

- [x] **B1 (R2). `sigmoid_alt_def` proved in 11 lines. DONE — reviewer correct.** Reviewer's one-liner:
      `unfolding sigmoid_def by (simp add: field_simps exp_minus)`. Currently a 9-line
      calculation in `Sigmoid_Definition.thy:13`.
- [x] **B2 (R2). `sigmoid_deriv_0`. DONE — reviewer correct.** Reviewer's one-liner:
      `by (simp add: sigmoid_derivative sigmoid_at_zero)`. Currently a metis-heavy block at
      `Asymptotic_Qualitative_Properties.thy:183`.
- [x] **B3 (R2). `sig_deriv_lim_at_top` / `sig_deriv_lim_at_bot`. DONE, but the reviewer's line does not work as written** — `unfolding sigmoid_derivative` cannot reach inside `deriv sigmoid`; it needs `sigmoid_derivative[abs_def]`. With that one attribute both proofs collapse from 39 and 38 lines to one. Cost: `HOL-Real_Asymp` becomes a session dependency, measured at no change in build time (0:38). Reviewer's one-liner:
      `unfolding sigmoid_derivative unfolding sigmoid_def by real_asymp`. Currently ~41 and
      ~30 lines. Note `real_asymp` is not used anywhere in this development; check the
      method is available under the session's parent.
- [x] **B4 (R2). DONE. `bounded_function` "phrased in a somewhat odd manner"**, equivalently
      `bounded (range f)`. Rather than churn 54 use sites, prove the equivalence as a lemma
      and cite it in the paper.
- [x] **B5 (R2). DONE. Dead lemmas.** `tendsto_exp_neg_at_infinity` is declared and never used —
      confirmed, the reviewer is right. `sig_deriv_lim_at_top` and `sig_deriv_lim_at_bot`
      are *also* unused. Decide per lemma: delete, or justify as part of the sigmoid's
      qualitative theory.
- [ ] **B6 (R2). A density corollary.** Reviewer 2: *"the theorem would be considerably
      easier to understand if the authors added a 'less constructive' version… that a
      certain set of functions constructed from sigma functions is dense in the set of
      continuous functions on an interval."* This is a genuine gap — the development has no
      such statement — and it is a short derivation from Theorem 2.1. Worth doing: it is
      the reviewer telling us exactly what would make the result legible.
- [ ] **B7 (R1). ε–N framework generalization** to join-semilattices → pseudometric spaces.
      Optional, and weigh against Reviewer 2, who thinks the ε–N material should not exist
      at all. These two reviewers directly conflict; see D1.
- [ ] **B8 (R1). p.12 l.41 "the right-hand side should be a natural number."** Locate the
      corresponding formal statement and check the typing.
- [ ] **B9. Sweep for other one-line-able proofs.** Reviewer 2's charge is "bloated", not
      "these three are bloated". A systematic pass over the sigmoid theory (the part they
      read) is the honest response. 59 `smt` calls remain, which read as sledgehammer output.

### B1–B5 outcome (verified 2026-09-05)

All five claims were tested in a scratch session against the built heap before being applied.
Four were correct verbatim; B3 was correct in substance but wrong as written. Net effect on
the four files: **105 lines deleted, 18 added**, 445 declarations unchanged, session builds
clean and the audit session passes. This is worth stating in the response letter: the
reviewer's specific criticisms were checked one at a time, and where he was right the code
changed.

## C. Paper / writing tasks

- [ ] **C1 (R1, R2, R3). Rewrite the constructivity claim.** State plainly: Isabelle/HOL is
      classical, we use classical reasoning throughout, and by "constructive" we mean the
      paper's sense — an explicit analytic form for the approximating sums — *not*
      intuitionistic provability and not code extraction. Then point at
      `mollifier_network`, whose coefficients are written out.
- [ ] **C2 (R3). Make the N story concrete.** R3: *"From the recipe given, it is not at all
      clear how easily one could obtain the necessary N… the authors should at least work
      out some examples and show that the value of N obtained is realistic. One could
      imagine obtaining an upper bound that works but is orders of magnitude larger than
      necessary."* This is the sharpest criticism in the whole review set and is **not yet
      answered**. See D2.
- [ ] **C3 (R1). Compare with Mathlib's sigmoid.** And state what is genuinely new — the
      n-th derivative closed form via Stirling numbers of the second kind.
- [ ] **C4 (R1). Justify the sigmoid theory's role.** The UAT needs only a generic bounded
      sigmoidal σ, so explain why the sigmoid-specific development belongs: it is what makes
      Corollaries 6.1–6.2 (prescribed logistic and Gompertz weights) possible, and those
      need the n-th derivative.
- [ ] **C5 (R1, R3). Restructure the UAT proof section**, separating informal intuition from
      formal statements. R3 also: three pages of informal proof of unoriginal mathematics is
      the wrong emphasis; describe *the formalization*, not the mathematics.
- [ ] **C6 (R1). Structured overview of the development**, not code fragments — theory
      graph, what each theory contributes, where each paper result lives.
      `PAPER_CORRESPONDENCE.md` is most of this already.
- [ ] **C7 (R1). Reproducibility statement**: Isabelle version (2025-2), the AFP entries
      required, build command, repository URL. Currently blocked on
      `Real_and_Complex_Analytic` not being in the AFP — say so explicitly rather than
      omitting it.
- [ ] **C8 (R1). Mark formalized vs sketched.** Every claim in the paper should say which.
      R1 flags the sigmoid's 0–1 bounds specifically; that one *is* formalized
      (`sigmoid_range`).
- [ ] **C9 (R3). Shorten §1.3.**
- [ ] **C10 (R1, R2). Typos**: "modeling[21]" and "Stirling.thy[4]" (missing space before
      citation), bracket scaling p.7 l.30 and p.8 l.49, "an recipe" p.10 l.42,
      "suffiiciently" p.10 l.46.

## D. Judgment calls — decide deliberately, do not just comply

- [ ] **D1. Reviewers 1 and 2 directly contradict each other on the ε–N material.** R1 calls
      it "a valuable addition" and wants it *generalized*; R2 says the lemmas are "trivial
      consequences of unfolding the filter-based definitions" and it "does not deserve a
      section all by itself". Both cannot be satisfied. R2 is right that filters are the
      ITP-standard idiom; R1 is right that the bridge has value. Suggested line: keep the
      lemmas, demote the section to a subsection, present them as a convenience bridge
      rather than a contribution, and do not claim novelty for them.
- [ ] **D2. Is the constructive N actually realistic?** R3's challenge is empirical and we
      currently cannot answer it. The formalization fixes `N > max(2(b-a)/δ, 3, 1/η)` with
      δ from uniform continuity — for a Lipschitz f this is computable. The honest options:
      (a) instantiate the bound for Example 7.1's f on [-5,5] and compare against the paper's
      own N = 25 and N = 50; (b) concede in the text that the bound is not sharp and say what
      it is good for. **(a) is the strong answer and is largely an Isabelle exercise.**
      Do not claim sharpness without checking — an unrealistic bound honestly reported is
      better than a claim a reviewer can puncture.
- [ ] **D3. Do not over-claim the counterexample.** Theorem 5.2's printed bound being false
      is the most striking new result, but it must be stated as a finding about a published
      theorem's printed constant, with the counterexample's hypotheses laid out, and with the
      replacement explicitly labelled non-sharp.
- [ ] **D4. Scope of the resubmission.** With the development now covering the whole paper,
      decide whether this is "a formalization of the UAT" (the old framing, which R2/R3
      correctly call modest) or "a formalization of Costarelli–Spigler that found two defects
      in it" (the new framing). The second is a different and much stronger paper.

## Suggested order

1. **B1–B5** — cheap, checkable, and they answer the reviewer who rejected. Fixing what he
   pointed at is the most direct evidence the criticism was taken seriously.
2. **B6** — the density corollary; small, and it is what R2 asked for.
3. **D2 / C2** — the N-realism question. The hardest and the most valuable.
4. **C1, D4** — reframe constructivity and the paper's scope.
5. **C3–C10** — the writing pass.
6. **B7** — only after D1 is decided.
