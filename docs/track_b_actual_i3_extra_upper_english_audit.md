# Track B — real Algorithm 5.4 I3 failures must expose an extra upper original
**Date:** 13 November 2026. **English proof precedes Lean.**

## What is already proved and what is genuinely new

The merged Track B PR #95 proves that, for two actual **unrestricted** finite `ambientPoolPrescribedData` source functions over one finite ambient model, the full source's old ordinary-L socle can be represented by a nonempty marked pool. Therefore any full/marked corrected-(B3) discrepancy needs an omitted upper L-reduct.

The real Algorithm 5.4 source is more selective: at cut `p`, let `Z=Envelope.closure (R.I (p+1)) X`. The pinned successor tree already defines
`closureSelectedOriginal family A hAvoid original Z p`: an original name is chosen precisely when *some real closure node strictly crossing p* is its prefix. The actual candidate source function `closureSelectedBoringData` is **definitionally** `selectedStagePoolPrescribedData` restricted to that predicate, not the larger all-eligible ambient pool. The previous unrestricted pool theorem cannot simply be quoted for it.

The following results address this exact mismatch without requiring a new, unjustified equality of arbitrary source functions.

## Theorem A — selected finite original pools have a common old L socle

Fix an arbitrary `A : EnumeratedPartialStructure db du dd`, `p < A.size`, a finite name map `original : Fin M → Fin A.size`, predicates `Full Marked : Fin M → Prop`, and one **eligible marked** name `w` with `Marked w` and `p+1 ≤ A.freeLevel (original w).val`.

Let `F=selectedStagePoolPrescribedData A p original Full` and `G=selectedStagePoolPrescribedData A p original Marked`. For every `S∈F.source`, use `selectedStagePoolPrescribedData_source_original` to extract a genuine selected name `v` with
`F.target S=A.partialTypeAt (p+1) (original v).val`.
The marked old type `T=A.partialTypeAt p (original w).val` is genuinely in `G.source` by `Marked w` AND its free-cut guard. The same source-original theorem supplies `u` with `G.target T=A.partialTypeAt (p+1) (original u).val` (the chosen target representative need not be w).

Apply `ambient_partialType_prescribedSocle` for `v` and `u` and reverse the second `SameInitialL` relation **in all four components**. Transitivity gives
```
∀ S∈F.source, ∃ T∈G.source,
  SameInitialL (prescribedOrdinarySocle (F.target S))
               (prescribedOrdinarySocle (G.target T)) p.
```
No injectivity of names, equality of upper L+ types, or choice-of-representative uniqueness is claimed.

## Theorem B — the missing upper reduct has an ACTUAL full-selected original witness

If `¬ F.CorrectedB3 family` and `G.CorrectedB3 family`, combine Theorem A with the checked `fullB3_failure_good_marked_missing_upper` to get an allowed complete upper reduct `U` in F absent in G.

Unpack `F.PrescribedUpperLType U`: it is witnessed by a source type `S∈F.source` with `U=(F.target S).lReduct`. Use the source-original theorem again to obtain a **specific** genuine name `v : Fin M` with `Full v`, `p+1 ≤ A.freeLevel (original v).val`, and `F.target S=A.partialTypeAt (p+1) (original v).val`. Hence
```
∃ v, Full v ∧ p+1≤freeLevel(original v) ∧
     ¬ G.PrescribedUpperLType
       ((A.partialTypeAt (p+1) (original v).val).lReduct).
```
This is a **concrete unmarked-upper-original** diagnostic; unlike the abstract dichotomy, it points to a name in the actual full source.

## Theorem C — genuine AlgorithmRun nonstructural I3

Let `R` be a real `SMTree.Envelope.AlgorithmRun` with seed `X` and run height `top`, with a seed at height top. Take `0<p<top`, `p<A.size`, and `p∈R.I 0`. Write `Z=Envelope.closure (R.I (p+1)) X`. Assume its real closure is represented by the fixed finite name pool `original`, and exclude both (I1) and (I2) on **this exact Z**.

The existing `R.finalLevel_interesting_of_run` together with `R.I_succ_eq_higher_final_of_run` identifies the selected p as genuinely interesting on Z. The checked `algorithmI3_failsCorrectedB3` then proves failure for **exactly the genuine closure crossing function**, whose definition is `selectedStagePoolPrescribedData` for `closureSelectedOriginal`.

If one marked predicate has an eligible name and its B3 test passes, invoke Theorem B. This yields a concrete upper original `v` with
`closureSelectedOriginal family A hAvoid original Z p v`, a real free-cut guard, and a complete upper L-reduct not among the marked permitted types. No separate assumed failure of B3, abstract source identification, or chosen fake auxiliary E-witness is introduced.

## Theorem D — actual finite numerical-H specialization (if reducible without extra hypotheses)

For `A=finiteNumericH K k N`, select `V=hStageOriginals K k N U (R.I 0)` and enumerate it by `V.equivFin`. The existing theorem `numericH_algorithmRun_closure_original_in_final_pool` discharges Theorem C's common-pool premise from genuine normalized forbidden-family avoidance and `X⊆ambientPrefixPool ... U`. This supplies an actual numeric-H corollary without assuming a finite pool by fiat.

## Hostile audit / safeguards

1. **Selected vs all-eligible:** `selectedStagePoolPrescribedData` must use the exact crossing `closureSelectedOriginal`, not the old `ambientPoolPrescribedData` on all names.
2. **Mark has a genuine member:** the marked original `w` requires BOTH `Marked w` and its actual `p+1` free cut; `Fin M` nonemptiness alone is insufficient.
3. **Target choice:** `selectedStagePoolPrescribedData` chooses ONE representative when two names share the same old type; no theorem says it chooses *every* named original's next type. Extract `v` from the *chosen target* with `source_original`.
4. **No-(I2):** actual closure crossings agree with this chosen source target only when (I2) is excluded. The more modest *failure* theorem already accounts for this via `algorithmI3_failsCorrectedB3`.
5. **The actual Z:** must use `R.I (p+1)` and no arbitrary/earlier pool; `R.I 0` is only for maintaining finite name pool and identifying final selection.
6. **No-(I1):** positive cut and no node at exactly p are separate from no-(I2), and are required to classify (I3).
7. **No new upper-upper constraints:** the forbidden B3 age witness lives in an arbitrary finite L-only continuation. We never copy its free upper-upper edges from ambient H.
8. **E is source data only:** all equalities of `A.partialTypeAt` used to represent actual crossings are full L+; the conclusion is only about their ordinary upper L-reducts.
9. **Same ambient A:** both selected profiles use one A and one p. Different occurrences/copies of a diary may have genuinely different full upper L-profiles even if their selected graph-age F agrees.
10. **K4 regression:** at cut 10, the verified numerical K4 gadget has an auxiliary q2=22 upper type absent from x=38-only marked source; no new unrestricted projection should be asserted.
11. **Correctly scoped conclusion:** an omitted full upper type is *necessary* for failure, not necessarily sufficient. No unverified finite witness realisation or common labelled monoid orbit follows.
12. **Empty profiles:** if there is no eligible marked original, Theorem A does not apply; treat that case separately rather than silently choosing a fake marked name.
13. **Run hypotheses:** the existence of a top seed, range `0<p<top`, exact pool representation and no-I1/no-I2 are not automatically implied by a generic interesting level.
14. **No protected-prose edits:** keep manuscript black text and existing TODO statuses untouched; update only the Lean validation ledger for precisely the proven endpoints after full exact-head CI.

## Gate

Implement A/B/C, optionally D if the named theorem interfaces match. Require complete hosted `lake build`, parser self-test and exact standard-only axiom reports (at merged PR #95 baseline: 408 + number of new named endpoints). Do not mark full resolved-diary B3 projection, the exact upper bound, or the common labelled source orbit green.
