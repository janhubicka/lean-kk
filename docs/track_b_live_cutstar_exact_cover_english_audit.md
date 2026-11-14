# Track B — exactness of live Kpt cut-star name cover
**14 November 2026. English proof and hostile audit committed before Lean, stacked on #175 and #174.**

## New point: live physical name matching is equivalent to type-spectrum inclusion

The stacked `IndexedCutStarLiveCover` relation from Track B PR #175 requires, for every **truly live** Kpt source j with complete old and upper `L^+` values and with positive physical ordinary-L cut-edge, a live Kpt source i on the other side with the SAME complete next ordinary-L reduct. No equality of old Kpt source, E bits, source-index cardinalities or multiplicities is required.

The already proposed theorem `indexed_cutStar_upperL_of_live_cover` proves the **forward implication**:
```
IndexedCutStarLiveCover A B c
  → ∀ R, IndexedPhysicalCutStarUpperL A c R →
         IndexedPhysicalCutStarUpperL B c R.
```
The missing reverse implication is equally important for an adversarial audit: it ensures that the physical name-matching condition has NOT secretly been made stronger than the actual projected profile inclusion.

### Theorem 1 — exact equivalence for directed live-node coverage

Suppose `∀ R, IndexedPhysicalCutStarUpperL A c R → IndexedPhysicalCutStarUpperL B c R`. Fix a genuine live j and a complete old/upper `L^+` pair T,U at cut c of node A(j), with `U.lReduct` physically L-adjacent to c. The definition itself gives:
```
IndexedPhysicalCutStarUpperL A c U.lReduct,
```
witnessed by EXACTLY j, T, U and the positive bit, with no arbitrary chosen source names. Apply the assumed upper-L inclusion to obtain `IndexedPhysicalCutStarUpperL B c U.lReduct`. Unpack its witness into a TRUE live i, complete old/upper records S,V of B(i), and `V.lReduct=U.lReduct`. This is precisely `IndexedCutStarLiveCover A B c`.

Thus
```
IndexedCutStarLiveCover A B c
  ↔ (∀R, IndexedPhysicalCutStarUpperL A c R →
         IndexedPhysicalCutStarUpperL B c R).
```
No no-(I2) assumption, finite index cardinality equality, common base E/k, or source pool exhaustiveness enters this *local projection* equivalence. Those hypotheses enter separately when relating the indexed predicate to an actual full finite Henson AlgorithmRun corrected-(B3) test.

### Theorem 2 — bilateral cover iff equality of projected spectra

Apply the preceding exact equivalence in both directions and pair the implications:
```
(IndexedCutStarLiveCover A B c ∧ IndexedCutStarLiveCover B A c)
  ↔ (∀R, IndexedPhysicalCutStarUpperL A c R ↔
         IndexedPhysicalCutStarUpperL B c R).
```
Empty positive-cut index spectra are correctly included: bilateral coverage is vacuous, and both spectra are empty. This is a set-level type comparison with physical witnesses, not a bijection of full dependent Kpt source nodes.

## Why this matters to the unresolved diary problem

The new equivalence shows that the proposed *physical name-to-name matching certificate* is neither under- nor overpowered for the precise local B3 cut-star spectrum. Therefore a subsequent refined diary proof can aim directly for a bilateral relation between **truly live** Kpt cut-neighbour nodes preserving their complete next ordinary-L types, rather than equality of full old/upper dependent L+ relations or a per-type quantification over abstract `RelationalPrefixType`.

An actual Henson AlgorithmRun source has a finite exhaustive index by Track C/Track B, but this equivalence does NOT construct a cross-occurrence map from the macrodiary. That independent geometric step, source-coordinate reindexing and full I1/I2 labelled orbit remain open.

## Hostile review (12)

1. `live c j=true` alone is insufficient: a crossing needs BOTH `some` old and `some` upper complete Kpt ancestor records from the SAME node j.
2. The physical positive-cut condition uses `U.lReduct.binary...`, not an E incidence.
3. Every negative and positive old-to-upper ordinary-L atom at c+1 is preserved through equality of `V.lReduct`; matching just the single cut-edge is insufficient.
4. No matching of upper–upper edges of arbitrary future B3 witnesses: they remain freely chosen.
5. Old dependent L+ values T,S and auxiliary E are permitted to differ, so this is genuinely weaker than Track E's full physical crossing-pair matching.
6. No conditions on index injectivity, equal cardinalities, named envelope parameters or multiplicities.
7. The logical statement holds for arbitrary Params types, not only finite Kpt carrier indexes; actual-run finiteness must be discharged separately.
8. Empty cases do not introduce fake anchor nodes or nonempty sources.
9. The only fixed coordinate is source cut c; distinct source rank cut labels require transport.
10. Every source on the right is genuinely LIVE and has both complete records, not a fake all-eligible ambient original.
11. The equivalence is about projected spectrum sets only; it does not imply equality of full structural I1/I2 events or common labelled monoid orbit.
12. The K4 q2 auxiliary source still counts whenever it contributes a positive physical ordinary-L cut type; selected macrodiary age F alone does not produce the live coverage relation.

## Strict CI gate

Commit English first, then implement two named theorem endpoints in `Kk/B3LiveCutStarCoverExact.lean`, import and register reports. This PR stacks on #175 (643 reports expected on its frozen baseline) and #174 (640). Target **645** exact named standard-only reports after both parents pass, or recompute after newer Track G/D/A/F merges. Full hosted `lake build`, axiom parser self-test and no sorryAx/custom axioms required. Do not alter protected black manuscript prose or global diary validation marks.
