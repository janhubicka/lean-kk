# Track D — strict central integration of four already verified finite B3 endpoints
15 November 2026. English-first source/provenance audit.

## Exact source and prior independent gates

The four theorem bodies are already merged from [PR #215](https://github.com/janhubicka/lean-kk/pull/215), exact tested head `2ccbba1ae73b376787191df519395a9d440824e9`.
Its [dedicated exact-head workflow 43719076327](https://github.com/janhubicka/lean-kk/actions/runs/43719076327) and [full repository workflow 43719076338](https://github.com/janhubicka/lean-kk/actions/runs/43719076338) both passed. The dedicated script compiled `Kk.B3CutVisibleNoNonempty` and checked all **four** names with standard-only transitive axioms. These are real finite mathematical theorems, not manuscript hypotheses for global BRDs.

The current central base was `lean-kk/main` at `8fb817b7b89bc658266160e9603eb796d82ca546`, with 793 distinct `#print axioms` lines (the current main can move concurrently).

## Exact planned modification

Add ONE import:
`import Kk.B3CutVisibleNoNonempty` in `Kk.lean`.

Append exactly four qualified `#check` / `#print axioms` pairs in `scripts/check_axioms.lean`:

1. `Kk.henson_fullB3_of_no_eligible_cut_neighbour`
2. `Kk.henson_fullB3_of_cut_visible_complete_outputs_no_nonempty`
3. `Kk.henson_cut_visible_fullB3_failure_implies_marked_failure_no_nonempty`
4. `Kk.henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty`

No theorem statements or proofs are changed. The expected central named-gate size is **797**. The four names must be unique and exact; no unverified PR #223 or #227 theorem is imported.

## Mathematical scope

The first theorem proves no genuine selected free-cut-eligible positive L cut neighbor implies corrected B3. The second proves the finite complete-chosen-type transfer without an independently nonempty marked source. The third is the negative failure implication. The fourth supplies a represented marked source and no-(I2) to derive chosen upper type coverage from actual positive physical full-cut neighbors belonging to marked names; it still assumes precisely that containment. In particular it does not identify the actual auxiliary parameter closure with selected macrodiary fronts, nor prove the full small-independent boringness or labelled source orbit.

## Adversarial checks

- Verify the four names actually occur in the source and in the merged exact-head dedicated gate.
- Keep original `Kk.lean` imports and existing axiom registrations untouched; add only.
- Exact central pin and total reports must be verified by a fresh full workflow; do not borrow the 793-report gate from another source commit.
- No `sorryAx`, custom axiom or admitted theorem may be introduced.
- No manuscript GREEN global theorem follows.
- Do not supersede other tracks' in-flight central imports or reorder existing report checks.
- Retain old `Kk/B3CutVisibleTransfer.lean` interfaces for historical source references.
