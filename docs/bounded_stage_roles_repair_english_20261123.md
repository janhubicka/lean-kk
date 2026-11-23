# Canonical generation bounds in resolved-Q stage-role contracts

## Status and defect

This is an English-first interface repair proposal. No Lean edit or compiler
run is claimed here. The independent review of
`positive_generation_stage_coherence_english_20261123.md` approves the bounded
mathematical contracts used below; this note maps the existing call closure
and the arithmetic regression to preserve during implementation.

The literal definition in
`SuccessorTree/V10/BlockOrder.lean` is

```
hPosition k j m = 2 * (k+1) * j + 2*m.
```

In particular, for every k and j,

```
hPosition k (j+1) 0 = hPosition k j (k+1).
hPosition k (j+1) k = hPosition k j (2*k+1).
```

Both follow by substitution and distributivity. The right-hand generation in
the first equality exceeds k. The second also exceeds k for every k, including
k=0. Thus uniqueness of real address decoding requires the canonical guard
`m ≤ k`; it is not an optional convenience for proof automation.

For a source-level contradiction in the old root contract, assume a root cap
v belongs to U and has address `hPosition k (j+1) k`. The unbounded contract
accepts the alternative presentation `v.val = hPosition k j (2*k+1)` and
therefore concludes `role j = .dummy`. If j is an earlier selected coding
base, `role j = .coded true` is contradictory. At k=2, this is exactly the
alias `16 = hPosition 2 2 2 = hPosition 2 1 5`. This does not show that an old
Lean theorem is false: it shows that its displayed application hypotheses can
exclude the intended resolved-Q source.

The same defect affects the Plan contract. A selected TOP at `hPosition 2 1 2`
also has address `hPosition 2 0 5`. The unbounded contract would require a
selected coding or retained auxiliary role at base 0, contrary to an initial
isolated dummy there.

## Correct contracts

For `K : AgeTestModel db du dd`, `U : Finset (Fin N)`, and Plan,
the root contract is

```lean
∀ v : Fin N, v ∈ U →
  ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
    role j = .dummy
```

The Plan contract is

```lean
∀ v : Fin N, v.val ∈ Plan →
  0 < (finiteNumericH K k N).freeLevel v.val →
  ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
    (role j = .coded true ∧ m = k) ∨
    (∃ block : Nat, role j = .auxiliary block true)
```

The one-cap concrete root contract is the corresponding specialization
`∀ j m, m ≤ k → cap.val = hPosition k j m → role j = .dummy`.
These contracts retain every canonical-generation assertion in the old
interfaces and remove only assertions about noncanonical presentations.
`hPosition_injective_bounded` then prevents the aliases above from applying.

## Complete source occurrence and call map

The repository-wide search for `hRootDummy`, `hPlanShape`, and the affected
theorem names found eight affected declaration signatures in four Lean files.
The existing names are listed to make the proposed change mechanically
reviewable; line numbers refer to the restored published baseline.

| Existing declaration | Location | Required local change | Downstream consumers |
| --- | --- | --- | --- |
| `resolvedQ_stage_name_shape_of_planned_levels` | `Kk/TrackDPlannedStageRoles.lean`, declaration 51, contracts 57/60, uses 85/87 | Bound both contracts; add `hm : m ≤ k` with the tested address and supply it in both membership branches. | The next two helpers in this table. |
| `resolvedQ_stage_omitted_positive_name_is_selected_top` | Same file, declaration 96, contracts 104/107, call 119 | Bound both contracts; add tested `hm : m ≤ k`; pass it to stage-name shape. | Full coverage, and the new positive-generation coherence proof. |
| `resolvedQ_stage_selected_base_has_no_retained_neighbour` | Same file, declaration 142, contracts 153/156, call 167 | Bound both contracts; add tested `hm : m ≤ k`; pass it to stage-name shape. | `henson_actualRun_selected_coded_lower_real_unselected`. |
| `resolvedQ_stage_full_base_coverage_of_planned_levels` | Same file, declaration 197, contracts 205/208, call 224 | Bound both contracts; rename the already present unused `_hm : m ≤ k` to `hm` and pass it to the positive-name helper. | Planned-stage marked-B3 actual-run endpoint. |
| `henson_actualRun_lower_real_unselected_of_planned_stage_markedB3` | Same file, declaration 241, contracts 287/290, call 325 | Bound both contracts; the base-coverage callback already supplies `hm`. No extra application hypothesis is needed. | No Lean theorem consumer found beyond its axiom/check script. |
| `henson_actualRun_selected_coded_lower_real_unselected` | `Kk/TrackDEmptyPhysicalCutStar.lean`, declaration 190, contracts 239/242, call 263 | Bound both contracts; pass the `hm` already returned by `finiteNumericH_eligible_lower_cut_neighbour_is_higher`. | No Lean theorem consumer found beyond its axiom/check script. |
| `henson_actualRun_selected_coded_lower_real_skip_of_no_seed` | `Kk/TrackDZeroStageActualRunSkip.lean`, declaration 203, contracts 238/241, uses 263/264 | Bound both contracts; retain the decoder's currently unused `_hm` as `hm` and pass it in each direct root/Plan membership branch. | Concrete top-seed selected-code skip. |
| `henson_topSeeds_selected_coded_lower_real_skip` | `Kk/TrackDTopSeedConcreteLowerSkip.lean`, declaration 97, contracts 131/133, local lifted root contract 165, call 172 | Bound the cap and Plan contracts; add and pass `hm` in the singleton-U root lifting; invoke the bounded no-seed skip. | No Lean theorem consumer found beyond its axiom/check script. |

The four check scripts refer to the declaration names without constructing
applications: `scripts/check_axioms_track_d_planned_roles.lean`,
`scripts/check_axioms_track_d_empty_star.lean`,
`scripts/check_axioms_track_d_zero_stage_skip.lean`, and
`scripts/check_axioms_track_d_concrete_topseed_skip.lean`.
They must still inspect and audit the repaired endpoints, not merely retained
unbounded compatibility declarations. The old English audits mention the two
selected-code applications and should be qualified with the present repair;
their historical proof order must not be represented as having checked these
new signatures.

No independent unbounded-generation contract was found elsewhere in the
current `.lean` sources by this identifier/call search. This is a scoped call
map, not a claim about all possible semantic variants of the condition.

## Recommended repair and compatibility decision

The call closure is small: eight declarations in four files, and the physical
decoders already provide every required bound. A consistent in-place signature
repair is the simplest implementation: preserve the public declaration names,
weaken root/Plan hypotheses, add a tested-address generation bound only in the
three low-level helpers that currently lack it, and propagate existing bounds
through the other five declarations. Existing local proof applications listed
above can then be updated directly. All ordinary-Q role theorems, source
representation lemmas, zero-column uniqueness results, and numerical-H
definitions remain unchanged.

If exact external API compatibility is required, the alternative is to add
eight bounded primary declarations with a `_bounded` suffix and retain the
old declarations explicitly as compatibility-only. The old first three
helpers cannot simply be obtained by calling their bounded replacements for
an arbitrary unbounded m; their old direct proofs must remain or be factored
through an internal membership lemma. At the five application endpoints whose
physical decoder supplies m≤k, an old unbounded caller may supply the bounded
contract by ignoring its extra bound argument. In either strategy, every new
actual resolved-Q application and every new endpoint audit must use the
bounded contract.

The root integrator should choose one strategy before Lean edits. Preserving
the old unbounded assumptions in the new positive-generation theorem is not a
valid repair, because it would leave the actual-source application obstruction
in place.

## Regression and proof obligations

1. Prove the universal address alias
   `hPosition k (j+1) 0 = hPosition k j (k+1)` from the literal definition.
2. Check a concrete root assignment at k=2 with base 1 selected coded and
   base 2 dummy: the bounded root contract for address 16 admits exactly
   its canonical dummy base, while the old unbounded contract would force
   the selected base 1 dummy via generation 5.
3. Check the analogous Plan address 10 with base 0 dummy and base 1 selected
   TOP; bounded decoding admits the intended Plan shape.
4. Keep positive free-level and actual stage-membership gates in every
   repaired Plan application.
5. Both physical decoder directions in positive-generation coherence must
   pass their own genuine `m ≤ k`, never a fabricated upper bound.
6. Recheck the eight repaired declaration signatures and their axiom reports;
   compiling only an unused new bounded helper would not validate the repaired
   concrete top-seed application.
