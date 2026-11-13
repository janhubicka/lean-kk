# Track C — attach complete old and upper L+ records to a single exhaustive per-run Kpt index

**13 November 2026. English proof and 15-point hostile audit BEFORE Lean.**
This is stacked on the Track C exhaustive-index branch `kk-track-c-exhaustive-run-index-20261113`; do not treat its declarations as already compiler-verified before exact-head CI.

## C14. Partial old/upper types of any actual Kpt node at a cut

For any `z : AdmissibleKptNode family` and `cut:Nat`, define two
**intrinsic** (choice-independent) options:

- `kptFullOldAtCut z cut`: if cut<lev z, the complete raw
  `LevelTree.ancestor z cut`, otherwise none;
- `kptFullUpperAtCut z cut`: if cut<lev z, the complete raw
  `LevelTree.ancestor z (cut+1)`, otherwise none.

Both values belong to the uniform dependent type
`RawPartialTypeNode db du dd`, which keeps the prefix length,
**all L and E atoms**, unary, diagonal, positive and negative data.
They depend on the actual Kpt node, not on its possible multiple
seed/parameter/meet decomposition witnesses.

When cut<lev z, each option equals `some` of the corresponding
literal complete ancestor. Otherwise **both** are none.

## C15. Every actual prescribed full-source input receives an INDEXED complete pair

Retain the physical numerical H+ structure, actual AlgorithmRun R,
the root seed prefix invariant and the actual pre-cut closure
`Z_cut = closure (admissibleKptSTree family) (R.I(cut+1)) X`.
Let V be the actual FINAL maintained original-name pool
`hStageOriginals K k N U (R.I 0)`, not all Fin N. At cut<runHeight
assume the exact full no-(I2) competing-meet condition on Z_cut.

Let `F = closureSelectedBoringData family A hAvoidA
  (hOriginalName V) Z_cut cut` be the full chosen source prescription.

Suppose `params` is the finite set of ALL nodes of final closure
Z_final, and `presentAt : Nat → Fin params.card → Bool`
satisfies the literal per-cut membership equivalence
`presentAt cut j=true ↔ (params.equivFin.symm j).val∈Z_cut`.
These data are constructed, not postulated, by the previous
Track C uniform-exhaustive-index theorem.

**Claim.** For every `T∈F.source`, there exists a SAME
`j : Fin params.card` with `presentAt cut j=true` and
`kptFullOldAtCut (params.equivFin.symm j).val cut =
   some (⟨cut,T⟩)`, and
`kptFullUpperAtCut (params.equivFin.symm j).val cut =
   some (⟨cut+1,F.target T⟩)`.

**Proof.** The previous, independently verified Track C
`finiteNumericH_run_final_pool_crossing_and_upper_types`
gives `IsCrossingGraphOf family Z_cut cut F` under the real
no-(I2) condition. So every T in F.source has an ACTUAL z∈Z_cut
strictly above cut whose consecutive complete raw ancestors are
exactly (T,F.target T). By closure monotonicity and the
`params`-exactness theorem, z occurs at a unique index j in
the one global final closure index. The exact `presentAt`
predicate for the SAME run makes j active at cut. The C14
definitions and predecessor identities then give the two
complete raw L+ type equations, with no replacement E expansion
on any finite L-age witness.

## C16. Construct the indexed assignments rather than assume them

Invoke C11 to CONSTRUCT one `params` and `presentAt` for
the entire run. All previous conclusions now hold for **every**
cut < runHeight satisfying no-(I2), using the SAME fixed
`Fin params.card` index, not a different finite parametrization
at each cut. The outputs are:
1. exact full final closure enumeration;
2. exact active-node mask at every pre-cut level;
3. complete old and upper L+ type assignments to every F source
   under no-(I2).

The index is canonical only **as a set of Kpt nodes within
one run**, not as an ordered numeric list across two occurrences.
Track E still must compare fully synchronized cuts and
literal source names or supply a bijection preserving those names,
active masks, upper types, ordered event frames and monoid images.

## Adversarial checklist

1. Noncanonical meet decompositions must not affect the assigned source identity: index real Kpt node values.
2. `params` indexes the COMPLETE final closure, not the finite original-name pool V; the two `Fin` domains differ.
3. `presentAt` tests actual membership in `R.I(cut+1)` closure, not in final closure alone.
4. `cut<lev z` is strictly required for the upper ancestor at cut+1.
5. Present-but-not-crossing nodes can occur and must have absent old/upper option assignments at that cut.
6. No-(I2) is essential for the selected `F.target` to cover **every** closure crossing with a unique output.
7. Preserve BOTH directions of `IsCrossingGraphOf`; source membership alone is insufficient.
8. Old+upper pair must come from the SAME z and the SAME j, not two separately chosen original witnesses.
9. `RawPartialTypeNode` records the complete dependent L+ including auxiliary E, fake predecessor bits, unary and diagonal fields.
10. The proof does NOT add E to an arbitrary corrected-B3 L-only age witness.
11. `Finset.equivFin` may not induce matching index numbers in two different runs; no cross-occurrence canonicality.
12. The full finite name pool V itself is not uniformly bounded in the manuscript's unbounded recursive schedule.
13. The truth of F.CorrectedB3 or any non-skippability classification does NOT follow from source indexing.
14. K4 extra cuts 10/22 remain actual auxiliary events, not selected-front boring levels.
15. No common labelled inverse monoid orbit or exact big Ramsey number is certified by these finite, conditional source identities.

Lean target: `Kk/NumericHIndexedUpperRecords.lean`.
Strict exact-head isolated build and all new named standard-only axiom
reports are mandatory. Leave the shared module aggregator and the
manuscript's protected black/olive text unchanged.
