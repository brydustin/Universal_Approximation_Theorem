# Legacy

Superseded files, kept under their original names for provenance. **None of
these build**, and none is part of the `Sigmoid_Universal_Approximation`
session: `ROOT` does not mention them, `open_sources.sh` globs only the
repository root, and `Proof_Audit.thy` reads only the root directory, so
nothing here is loaded or checked.

| File | Superseded by | Why it does not build |
|---|---|---|
| `Universal_Approximation.thy` | `Universal_Approximation_1d.thy` and the 27 other theories at the root | imports a `Sigmoid` theory that is no longer part of the development |
| `Paper_5_2_Counterexample.thy` | `Theorem_5_2_Counterexample.thy` (same content, renamed) | imports `Paper_Multivariate`, a theory that has been dissolved |

`Universal_Approximation.thy` is the original single-theory draft of the whole
formalization. `Paper_5_2_Counterexample.thy` is a pure rename: the current
file differs from it only in its theory name, its import, and an added section
heading.

Two further theories, `Paper_Corollaries.thy` and `Paper_Multivariate.thy`,
were removed rather than renamed. Every declaration they held survives, moved
to the theory whose result it refines, so no copy is kept here; the originals
are in the history at the commit before "Dissolve the Paper_ theories".
