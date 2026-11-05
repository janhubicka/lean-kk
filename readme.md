# lean-kk

Lean 4 validation for the big Ramsey degree project on universal `K_k`-free graphs, using the pinned [`lean-successors`](https://github.com/janhubicka/lean-successors) type-respecting Ramsey theorem.

**Verified building blocks:** finite-family type-respecting Ramsey refinement and conditional labelled orbit transfer; normalized Henson graph-language encoding and integer-witness graph-age canonicalization; actual canonical cover-block arithmetic and **arbitrary-subfront cover-or-equality** by a zero-supported relative-age lift; selected-original and full AlgorithmRun I3 bounds under their precise hypotheses; genuine finite families of isolated reserved original clique blocks; one-step Henson selected extensions with explicitly certified complete mixed-neighbourhood tests; exact linked-clique-capacity insertion and nonmonotone live-pool update; safe deletion-only capacity transfer; and the **exact literal numerical-H binary L column** of a genuinely later top-generation selected original against EVERY earlier original at EVERY generation, plus all-generation old-to-new reserved nonedges and designated positive clique atoms in an actual one-step construction. These are kernel-checked conditional statements with named transitive-axiom reports. None proves that the prescribed infinite resolved-copy diary satisfies all original-edge, full B3 and common-orbit requirements.

**Not proved by this library:** the proposed resolved numerical-H copy's mixed-parameter extension admissibility, equality of full parameter-closed envelope records for two occurrences of the same macrodiary, a common labelled inverse-source orbit, or the unconditional upper and lower big Ramsey bounds. In particular, selected-only age preservation does **not** imply full corrected (B3) preservation.

The counterexample modules (`GraphAgeShadow`, `K4AuxiliaryShadow`, `UniformAuxiliaryShadow`, and the genuine numerical-H `K4FullVsMarkedB3`) are intentional regression tests for invalid shortcuts. They are not candidate routes to the upper bound.

See [the current status and dated evidence](docs/validation.md) for the exact theorem interfaces, counterexamples, open obligations, and CI run links.

## Build and axiom audit

```sh
lake update
lake exe cache get
lake build
lake env lean scripts/check_axioms.lean
```

The transitive axiom audit checks the named theorem endpoints, not whether their hypotheses have been discharged for the manuscript's application. Changes must pass the full build before being described as Lean-validated.
