# lean-kk

Lean 4 validation for the big Ramsey degree project on universal `K_k`-free graphs, using the pinned [`lean-successors`](https://github.com/janhubicka/lean-successors) type-respecting Ramsey theorem.

**Verified building blocks:** finite-family type-respecting Ramsey refinement and conditional labelled orbit transfer; normalized Henson graph-language encoding and integer-witness graph-age canonicalization; actual canonical cover-block arithmetic and **arbitrary-subfront cover-or-equality** by a zero-supported relative-age lift; selected-original and full AlgorithmRun I3 bounds under their precise hypotheses; genuine finite families of isolated reserved original clique blocks; one-step Henson selected extensions with explicitly certified complete mixed-neighbourhood tests; exact linked-clique-capacity insertion and nonmonotone live-pool update; safe deletion-only capacity transfer; and the **exact literal numerical-H binary L column** of a genuinely later top-generation selected original against EVERY earlier original at EVERY generation, plus all-generation old-to-new reserved nonedges and designated positive clique atoms in an actual one-step construction; and the **exact incoming auxiliary E-column and selected free level** of the same physical finite top original, including fake numeric sources. The concrete K4 seeded AlgorithmRun has already been proven to select BOTH auxiliary cuts 22 and 10, with the Kpt parameter at 22 in the real closure at cut 10. These are kernel-checked conditional statements with named transitive-axiom reports. None proves that the prescribed infinite resolved-copy diary satisfies all original-edge, full B3 and common-orbit requirements.

**Not proved by this library:** the proposed resolved numerical-H copy's mixed-parameter extension admissibility, equality of full parameter-closed envelope records for two occurrences of the same macrodiary, a common labelled inverse-source orbit, or the unconditional upper and lower big Ramsey bounds. In particular, selected-only age preservation does **not** imply full corrected (B3) preservation.

The counterexample modules (`GraphAgeShadow`, `K4AuxiliaryShadow`, `UniformAuxiliaryShadow`, and the genuine numerical-H `K4FullVsMarkedB3`) are intentional regression tests for invalid shortcuts. They are not candidate routes to the upper bound.

See [the current status and dated evidence](docs/validation.md) for the exact theorem interfaces, counterexamples, open obligations, and CI run links.

**8 November verification:** the repaired numerical-H parameter closure, chronological propagation through actual AlgorithmRun stages, and exact finite isolated-block continuation criterion pass the full local build and **305 exact named standard-only axiom reports**. The [verification record](docs/audits/2026-11-08-local-validation.json) identifies the exact source revision, all source hashes and dependency pins, and every named report. [PR #70](https://github.com/janhubicka/lean-kk/pull/70) has also passed its separate hosted **297-endpoint** gate and merged at `fffb92e1a00a8b9978d5be245a0e4c8020eadcd1`; its merged tree matches the hosted-tested tree. PR #72 and #73 subsequently passed their separate hosted Lean gates and merged into main on 10 November 2026 (merge commits `ea4c3ee540381bd5179ac9261d07380072968c0e` and `9623dde0c5c0f872548fd6da99806a00010b0703`). The next exact single-block numerical-H generation-gate capacity theorem is on a separate English-first branch: only its abstract pair-gate lemma has a new local Lean check so far. The finite gluing theorem still needs its actual numerical-H prefix, simultaneous-front-column and canonical-age adapters.

## Build and axiom audit

```bash
set -euo pipefail
lake update
lake exe cache get
lake build
lake env lean scripts/check_axioms.lean | tee axioms.log
python3 scripts/check_axiom_report.py --self-test
python3 scripts/check_axiom_report.py scripts/check_axioms.lean axioms.log
```

The transitive axiom audit checks the named theorem endpoints, not whether their hypotheses have been discharged for the manuscript's application. Changes must pass the full build before being described as Lean-validated.
