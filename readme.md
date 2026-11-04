# lean-kk

Lean 4 validation for the big Ramsey degree project on universal `K_k`-free graphs, using the pinned [`lean-successors`](https://github.com/janhubicka/lean-successors) type-respecting Ramsey theorem.

**Verified building blocks:** finite-family type-respecting Ramsey refinement and conditional labelled orbit transfer; normalized Henson graph encoding and integer graph-age canonicalization; selected-original and full AlgorithmRun I3 bounds under their displayed hypotheses; genuine finite chains of isolated reserved original cliques; complete one-step Henson selected extensions after fresh blocks and under explicit older-block linked-capacity budgets; the **exact directed one-vertex recurrence** for linked clique capacity, including zero growth; and the **exact four-quadrant update** when both old/new live reserved witnesses and unreserved positive candidates change (including deactivations, new gap originals and changed block-tag spaces); and **deletion-only safety transfer**, showing that shrinking both positive candidate and live reserved sets cannot increase the linked budget, while inclusion of the entire next positive-neighbourhood set preserves a negative complete checker. The new recurrence is proved over the actual original edge table and is NOT a theorem that the proposed infinite macrodiary satisfies its per-stage hypotheses. All named Lean endpoints are built and checked with the strict transitive-axiom audit.

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
