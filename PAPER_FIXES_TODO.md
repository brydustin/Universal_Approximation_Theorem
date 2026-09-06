# Costarelli–Spigler fidelity fixes

Started 2026-09-05 from `PAPER_AUDIT_2026-09-05.md`.
Keep this checklist current; a box is checked only after source verification.

## Correspondence labels

- [x] Add short `(* ... *)` correspondence comments to every lemma, theorem and corollary (415 declarations after the structural repair below; zero missing).
- [x] Label definitions of the paper's operators and function classes by equation/definition number, or identify their unnumbered passage.
- [x] Identify unnumbered supporting results as auxiliary steps for their enclosing paper result; identify supplementary results honestly.

## Mathematical corrections

- [x] Separate endpoint sampling of f from midpoint radial centers in equation (5.1).
- [x] Verify the exact operator's uniform approximation (Theorem 5.1).
- [x] Verify its continuous-target and general-target Lp approximation on the normalized cube (Theorems 5.3 and 5.4).
- [x] Cover independently translated coordinate intervals for uniform approximation, with the paper's square as a specialization.
- [x] Export translated-domain Lp versions of Theorems 5.3 and 5.4 using measure transport; the earlier Lp statements used [a,b]^d only.

  Follow-up implementation checklist:
  - [x] Prove completed-Lebesgue measure and Lp error transport under translation.
  - [x] Export Theorem 5.3 on independently translated equal-length coordinate intervals.
  - [x] Export Theorem 5.4 with the original target's mollifier-integral coefficients on those intervals.
  - [x] Verify coefficient translation identities and label all supporting results.
  - [x] Rebuild from source, repeat the permanent audit, and update the correspondence report.

- [x] Assemble Corollary 6.1 with the prescribed logistic weight, a common N, f, and all derivative orders through n.
- [x] Assemble Corollary 6.2 with the prescribed Gompertz weight and the same joint conclusion.
- [x] Remove global Borel measurability of target representatives from the final Theorems 3.2/5.4, using completed-Lebesgue measurability on the approximation domain and almost-everywhere representatives.
- [x] Retain and explain the activation measurability requirement for ordinary Lebesgue Lp statements; do not silently replace it by continuity.
- [x] Give Theorem 4.2 in the paper's quantitative form, including strict supremum bounds and an explicit admissible consistency constant.
- [x] Check Theorem 5.2's quantitative bound for the exact operator: prove a counterexample to the printed formula and a valid, explicitly different replacement bound.
- [x] Complete the general-Lp mollifier construction and its coefficient-based approximation corollaries, without assuming the target globally bounded or continuous.
- [x] Ensure public Lp norm statements cannot use unspecified out-of-domain values as approximation evidence.

## Structural repair (2026-09-05, after the dead-code audit)

- [x] Remove the two unused mollifier developments: the (real,'n) vec construction and its plain-real copy. Only four dimension-generic measure lemmas were reachable from any stated result; they moved into `Lp_Inequalities.thy`.
- [x] Keep the density theorem, which is genuinely needed — including inside the paper's own mollifier proof — in its own theory `Lp_Density.thy`, named for what it proves.
- [x] Collect the restriction/zero-extension/representative bookkeeping in `Lp_Restriction.thy`, below every theorem that uses it, so the mollifier construction no longer imports through Theorems 3.2 and 5.4.
- [x] Rename the paper-construction theories to `Mollifiers.thy`, `Mollifier_Networks.thy` and `Translated_Lp_Approximation.thy`, and drop the `paper_` prefix from their constants and lemmas, now that no competing mollifier exists.
- [x] Derive the existential Lebesgue-target Theorems 3.2 and 5.4 from the constructive ones, so the paper's construction is on the path to a stated result rather than a leaf.
- [x] Derive the printed Borel-target Theorems 3.2 and 5.4 from those in turn, so that no stated result is proved by the density route and density survives only inside the mollifier convergence proof.
- [x] Add the strict supremum form of Theorem 4.1 for an arbitrary bounded sigmoidal activation, matching the printed norm conclusion; the earlier statement was pointwise.
- [x] Record the paper's radial-basis-function commentary before Theorem 5.1 and in Remark 5.1, and the fact that Remark 5.2's transposed sum (5.3) is the r0 parameter's second instance.
- [x] Add a machine-checked bridge between grid_point and sigma_anchor at positive heights, so the two center functions cannot silently drift apart.
- [x] List Definition 2.1, Lemma 2.1, Lemma 5.1, Remark 5.2 and the RBF commentary in the correspondence table.
- [x] Add `Numerical_examples.thy` covering Section 7: the three example functions exactly as printed, the proof that the displayed f' is the derivative of (7.1), membership of (7.2) in L^1(R), continuity of the bivariate target, and each example exhibited as an instance of the theorem the paper invokes for it. The figures and the reported numerical errors are explicitly not claimed.

## Documentation and final verification

- [x] Correct obsolete whole-paper completion claims and misleading statements about `undefined`.
- [x] Update the correspondence table to describe the final results and any remaining qualifications.
- [x] Rebuild all project theories from source, with `quick_and_dirty = false`.
- [x] Repeat the stored-fact oracle, hidden-hypothesis and free-variable checks.
- [x] Leave Isabelle using the parent library heap so all project theories continue loading from source.

## Progress notes

- Initial audit: all 20 source theories built; 402 stored project facts had no oracle dependencies, hidden hypotheses or fixed free term variables. That verified the old statements, not their full correspondence with the paper.
- Preserve user edits and existing proofs while correcting the specifications. The numerical experiments in Section 7 are outside these theorem repairs; illustrative unnumbered examples will be identified in the correspondence documentation.

## Verification of this repair pass

### Follow-up: explicit general-Lp mollification

- [x] Define the exact exponential bump of (3.3), in a dimension-generic form, and prove its smoothness, support, positivity and normalization.
- [x] Prove the normalized convolution Lp contraction and general-target approximate-identity convergence, including whole-space convergence.
- [x] Apply the construction to the completed-Lebesgue zero extensions (3.1)/(5.4), without boundedness or continuity assumptions on the target.
- [x] Export the integral coefficient formulas following (3.4) and their multivariate counterparts, and prove approximation by those networks.
- [x] Rebuild the full source session, repeat the audit, and update correspondence/remaining-work documentation.

The verification record below describes the preceding repair pass, not these new items.

Final full source build: **PASS**, 2026-09-05 14:03:32 America/Chicago,
Isabelle2025-2, `quick_and_dirty = false`, exit status 0. The build also regenerated
`output/document.pdf`.

- All 25 local theory files are in the audited import closure.
- All 403 lemma/theorem/corollary declarations have adjacent correspondence comments; zero missing.
- 450 stored project fact entries: no transitive oracle dependencies, no hidden theorem hypotheses,
  and no fixed free term variables.
- All 41 project axioms reported by Isabelle are generated definitional equations;
  no non-definitional project axioms were found.
- Source search found no `sorry`, `oops`, `skip_proof`, or `axiomatization` commands.
- `open_sources.sh` passes `bash -n` and was launched with all 25 source files.
  The running prover's actual `PolyML.SaveState.loadHierarchy` ends at
  `Real_and_Complex_Analytic`; it does not include a project heap.

The permanent audit is in `Proof_Audit.thy`; this run's exported messages are at
`/tmp/sigmoid_verified_fixes_final/Sigmoid_Universal_Approximation.Proof_Audit/PIDE/messages`.
The temporary export is supporting evidence, not required to repeat the audit.

This preceding repair milestone was **not a claim of complete paper reproduction**.
Its then-open mollifier-construction item is addressed by the follow-up above;
the translated-domain Lp item remains open. The false printed Theorem 5.2 bound
must not be marked as proved.

### Verified follow-up: explicit mollifier construction

Final full source build: **PASS**, 2026-09-05 14:56:41 America/Chicago,
Isabelle2025-2, `quick_and_dirty = false`, exit status 0. This build includes
the final coefficient-integrability lemmas and regenerated `output/document.pdf`.

- All 27 local theory files are in the audited import closure.
- All 462 lemma/theorem/corollary declarations have adjacent correspondence comments; zero missing.
- 525 stored project fact entries: no transitive oracle dependencies, no hidden theorem
  hypotheses, and no fixed free term variables.
- All 50 project axioms reported by Isabelle are generated definitional equations;
  no non-definitional project axioms were found.
- The new theories contain no `sorry`, `oops`, `skip_proof`, or `axiomatization` commands.
- `Paper_Mollifier_Construction.thy` (since renamed `Mollifiers.thy`) proves the exact bump, normalization, completed-Lebesgue
  zero-extension identities, local and whole-space Lp convergence, and integrability of
  every coefficient integral for general Lp targets.
- `Paper_Mollifier_Networks.thy` (since renamed `Mollifier_Networks.thy`) gives the explicit integral coefficients and the resulting
  one-dimensional and multivariate approximation theorems. Density is used internally
  to prove convergence of the specified mollifier, not as a substitute construction.
- The existing source-loading launcher automatically includes the two new theories;
  its parent-heap configuration is unchanged.

The permanent audit remains in `Proof_Audit.thy`; this run's exported messages are at
`/tmp/sigmoid_mollifier_verified/Sigmoid_Universal_Approximation.Proof_Audit/PIDE/messages`.
The correspondence report and historical Theorem 3.2 plan now point to these results.
This completes the explicit-mollifier follow-up, not the remaining translated-domain
Lp formulation or the entire paper without its documented qualifications.

### Verified structural repair

Clean full source build (`isabelle build -c`, so nothing was reused): **PASS**,
2026-09-05 18:06:59 America/Chicago, Isabelle2025-2, `quick_and_dirty = false`,
exit status 0, zero error messages, 0:47 session time. `output/document.pdf` regenerated.

- 28 local theory files, all in the audited import closure. `Proof_Audit.thy`'s ML block ran
  to completion (27.2 s), so its checks all held: every local `.thy` loaded, no transitive
  oracle dependencies, no hidden theorem hypotheses, no fixed free term variables, and no
  non-definitional project axiom.
- Source search finds no `sorry`, `oops`, `skip_proof` or `axiomatization`.
- 415 lemma/theorem/corollary declarations, all with adjacent correspondence comments; zero
  missing.
- Deleted: the `(real,'n) vec` mollifier development (48 declarations, of which 4 were
  reachable from any stated result) and the plain-real copy of the same construction
  (26 declarations, none reachable). Their four dimension-generic measure lemmas
  — affine invariance of the `lborel` Bochner integral, and Borel-implies-`lebesgue_on`
  measurability — were kept, in `Lp_Inequalities.thy`. Project declaration count fell from
  522 to 451.
- The two constructive theorems `mollifier_approximation` and
  `multivariate_mollifier_approximation` are now used, by `Lp_Representatives.thy`; the
  mollifier stack is no longer a leaf of the dependency graph.
- `continuous_dense_Lp` remains necessary and is used three times, including inside the
  paper's own mollifier proof (`compact_continuous_dense`). Removing the duplicate mollifiers
  did not remove the density route, and does not claim to have.
- `sigmoidal_Lp_approximation_theorem_general` and its multivariate counterpart keep their
  independent density-based proofs; they are the printed Borel-target statements.

### Verified constructivity and fidelity pass

Clean full source build (`isabelle build -c`): **PASS**, 2026-09-05 18:43:09 America/Chicago,
Isabelle2025-2, `quick_and_dirty = false`, exit status 0, zero error messages, 0:46 session
time. `Proof_Audit.thy` ran to completion (25.7 s), so all its checks held.

- 417 lemma/theorem/corollary declarations, all with adjacent correspondence comments.
- No `sorry`, `oops`, `skip_proof` or `axiomatization`.
- `continuous_dense_Lp` is now used by exactly one theory, `Mollifiers.thy`, inside
  `compact_continuous_dense`. Every stated Lp theorem reaches its conclusion through the
  paper's mollifier; none is proved by the density route.
- The remaining statements that quantify existentially over a continuous function are the
  four Theorem 3.2 / 5.4 forms and `continuous_dense_Lp` itself. That is the paper's own
  statement shape ("there exists N and a linear combination G_N"); the witness in each case
  is now the explicit mollified target, and the coefficient-explicit companions are
  `mollifier_approximation`, `multivariate_mollifier_approximation`,
  `translated_mollifier_approximation` and `square_mollifier_approximation`.
- Constructivity here is the paper's sense: an explicit analytic form for the sums. It is not
  executability. The development is classical, uses choice for almost-everywhere
  representatives, and generates no code.

### Verified Section 7 pass

Clean full source build (`isabelle build -c`): **PASS**, 2026-09-05 20:58:46 America/Chicago,
Isabelle2025-2, `quick_and_dirty = false`, exit status 0, zero error messages, 0:46 session
time. `Proof_Audit.thy` ran to completion (29.0 s), so all its checks held.

- 29 local theory files, all in the audited import closure; 445 lemma/theorem/corollary
  declarations, all with adjacent correspondence comments.
- No `sorry`, `oops`, `skip_proof` or `axiomatization`; no `smt` call in the new theory.
- `Numerical_examples.thy` adds `HOL-Analysis.Interval_Integral` to the session's imports,
  for the improper fundamental theorem of calculus used to integrate the majorant of (7.2).
