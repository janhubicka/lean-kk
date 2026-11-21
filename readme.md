# lean-kk

Lean 4 validation for the big Ramsey degree project on universal `K_k`-free graphs, using the pinned [`lean-successors`](https://github.com/janhubicka/lean-successors) type-respecting Ramsey theorem.

**Verified building blocks:** finite-family type-respecting Ramsey refinement and conditional labelled orbit transfer; normalized Henson graph-language encoding and integer-witness graph-age canonicalization; actual canonical cover-block arithmetic and **arbitrary-subfront cover-or-equality** by a zero-supported relative-age lift; selected-original and full AlgorithmRun I3 bounds under their precise hypotheses; genuine finite families of isolated reserved original clique blocks; one-step Henson selected extensions with explicitly certified complete mixed-neighbourhood tests; exact linked-clique-capacity insertion and nonmonotone live-pool update; safe deletion-only capacity transfer; and the **exact literal numerical-H binary L column** of a genuinely later top-generation selected original against EVERY earlier original at EVERY generation, plus all-generation old-to-new reserved nonedges and designated positive clique atoms in an actual one-step construction; and the **exact incoming auxiliary E-column and selected free level** of the same physical finite top original, including fake numeric sources. The concrete K4 seeded AlgorithmRun has already been proven to select BOTH auxiliary cuts 22 and 10, with the Kpt parameter at 22 in the real closure at cut 10. These are kernel-checked conditional statements with named transitive-axiom reports. None proves that the prescribed infinite resolved-copy diary satisfies all original-edge, full B3 and common-orbit requirements.

**Not proved by this library:** the proposed resolved numerical-H copy's mixed-parameter extension admissibility, equality of full parameter-closed envelope records for two occurrences of the same macrodiary, a common labelled inverse-source orbit, or the unconditional upper and lower big Ramsey bounds. In particular, selected-only age preservation does **not** imply full corrected (B3) preservation.

The counterexample modules (`GraphAgeShadow`, `K4AuxiliaryShadow`, `UniformAuxiliaryShadow`, and the genuine numerical-H `K4FullVsMarkedB3`) are intentional regression tests for invalid shortcuts. They are not candidate routes to the upper bound.

See [the current status and dated evidence](docs/validation.md) for the exact theorem interfaces, counterexamples, open obligations, and CI run links.

**21 November Track B verification:** [PR #422](https://github.com/janhubicka/lean-kk/pull/422)
passed the [complete hosted gate](https://github.com/janhubicka/lean-kk/actions/runs/44911987872):
**9,729 Lean build jobs**, parser self-test, and **961 exact named transitive-axiom
reports**, using only `propext`, `Classical.choice`, and `Quot.sound`.
Source `9292e833366cb5f113f300b6cbbf6f10eb0864d4` and the actual tested merge
`b4db7c2a9be750427dc8918616d5a35f0a738069` have the same tree
`2d730ed5e85f3c54e059c7912538c47eb6a84b5b`. All earlier 955 report names are
retained, with six new endpoints in `ControlledPivotBudget` and
`PhysicalControlledCoding`. The
[English proof and audit](docs/track_b_nonfree_pivot_residual_english_audit_20261121.md)
were committed first at `5f34e9015dd0943a02054118b2d018fdf68dc3c2`.

**Controlled coding now has a proved physical step:** the controlled cap and
growth conditions derive every joint linked-neighbour budget, including the
largest admissible support. Coding at the same selected nonfree pivot preserves
the complete canonical survivor age, and one finite Henson stage retains all
protected columns. A separate endpoint identifies the genuine chronological
cut `[0,v) → [0,v+1)`. This verifies Section 6 of the English note; its general
residual operation in Sections 1–5 remains English-only. The next task is
controlled-pre-age `C ≤ P` preparation with correct chronology and history,
followed by full Kpt/(B3), common-orbit, and infinite-diary transport.
[Exact evidence and six endpoint names](docs/audits/2026-11-21-track-b-controlled-pivot.json)
record the verified scope; no completed local full gate is claimed.

The entries below are historical checkpoints. Their open-task descriptions
refer to their dates and are superseded by the current status above.

**20 November Track B verification:** [PR #414 integration](https://github.com/janhubicka/lean-kk/actions/runs/44781646067) passed the complete hosted **9,727-job build**, parser self-test, and **955 exact standard-only reports** for head `4a275de622617da97a132ab8b8adf17cbb989c7b`. The actual CI merge `0792d8f297325eb5c80f807c2010a702789f77ac` includes newer main `ddf60ae5ddba9fbc846dd3072dabc44fdc829ea5`; all 932 main names are preserved alongside the 23 Track B names (17 new and six restored). The five proof modules are unchanged from the historical 953-report checkpoint `a433ad84f3881da535ee3e7164ff32e3337d2c3c`, so that manuscript pin remains valid. Canonical ages now transport through arbitrary sort maps, and an actual free split has a constructed finite numerical stage with the exact canonical restriction for every parent. Selected-pivot controlled coding and full Kpt source/orbit synchronization remain open. [Separate checkpoint and integration evidence](docs/audits/2026-11-20-track-b-canonical-splits.json) records hashes and scope; no completed local full gate is claimed.

**8 November verification:** the repaired numerical-H parameter closure, chronological propagation through actual AlgorithmRun stages, and exact finite isolated-block continuation criterion pass the full local build and **305 exact named standard-only axiom reports**. The [verification record](docs/audits/2026-11-08-local-validation.json) identifies the exact source revision, all source hashes and dependency pins, and every named report. [PR #70](https://github.com/janhubicka/lean-kk/pull/70) has also passed its separate hosted **297-endpoint** gate and merged at `fffb92e1a00a8b9978d5be245a0e4c8020eadcd1`; its merged tree matches the hosted-tested tree. PR #72 and #73 subsequently passed their separate hosted Lean gates and merged into main on 10 November 2026 (merge commits `ea4c3ee540381bd5179ac9261d07380072968c0e` and `9623dde0c5c0f872548fd6da99806a00010b0703`). The next exact single-block numerical-H generation-gate capacity theorem is on a separate English-first branch: its abstract pair-gate formula and generic injective image-capacity transport have five new local named Lean checks, but the actual numerical-H coordinate/edge correspondence is still open. The finite gluing theorem still needs its actual numerical-H prefix, simultaneous-front-column and canonical-age adapters.

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
