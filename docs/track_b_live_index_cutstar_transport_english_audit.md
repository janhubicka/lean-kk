# Track B — physical live-index cut-star matching for two real AlgorithmRuns
**14 November 2026. English argument and adversarial audit committed before Lean.**
This PR stacks on [two genuine runs PR #174](https://github.com/janhubicka/lean-kk/pull/174) and must not merge until that parent passes exact-head CI and is integrated.

## Purpose and genuine improvement

The finite two-run theorem from the parent branch constructs ONE true exhaustive final Kpt-node index for each actual Henson AlgorithmRun, together with exact per-cut `presentAt` masks and complete dependent OLD/UPPER `L⁺` types. Its full-(B3) comparison still has an abstract hypothesis that the sets of projected positive-cut complete upper ordinary-`L` reducts agree.

For an application to a refined diary we need to check source names, not quantify over an opaque whole type predicate. We therefore prove a concrete name-by-name comparison which is **STRICTLY WEAKER** than Track E's full OLD/UPPER `L⁺` pair matching. In particular it allows a Kpt node j of one run to correspond to a different Kpt node i of the other whose OLD dependent Kpt type is NOT equal, provided both genuinely cross the cut and have the SAME COMPLETE next ordinary-`L` type.

## Definition — physical live cut-star source cover, one direction

For actual Kpt node indices `nodeA : IA→AdmissibleKptNode family`, `nodeB : IB→AdmissibleKptNode family` and per-cut Boolean masks `liveA,liveB`, define `IndexedCutStarLiveCover family nodeA liveA nodeB liveB c` to mean:

For every index j∈IA and every complete old and upper `L⁺` partial type pair (T,U), if:
- `liveA c j=true`, i.e. this is a TRUE active Kpt source node at the selected stage;
- `kptFullOldAtCut(nodeA j)c=some(c,T)` and `kptFullUpperAtCut(nodeA j)c=some(c+1,U)`: j genuinely crosses the cut and is assigned BOTH records from the same real Kpt node;
- `U.lReduct.binary (some (Fin.last c)) none 0=true`: its complete upper ordinary-`L` reduct has a genuine **POSITIVE ORDINARY-L edge to the tested cut**;

then there exist an index i∈IB and complete physical records (S,V), with `liveB c i=true`, both genuine old and upper records of nodeB i, and **equality of COMPLETE ordinary-L upper reducts** `V.lReduct=U.lReduct`.

The matching relation is not a bijection, not an injection, does not preserve the old `L⁺` source type, E columns, parameter-address labels, or Kpt source-index multiplicity. It need not match upper types that are NON-adjacent to c, because the verified Henson full-B3 cut-star normal form discards those types.

## Theorem A — live name cover gives one-sided upper-type inclusion

If `IndexedCutStarLiveCover A B c`, then:
```
∀R, IndexedPhysicalCutStarUpperL A c R → IndexedPhysicalCutStarUpperL B c R.
```
Proof: unpack R to a true physical Kpt-node index j, complete old/upper (T,U), and positive ordinary L cut-edge. Apply the directional live cover to obtain true index i and complete upper V in B with `V.lReduct=U.lReduct=R`. Use the EXACT same positive R edge to conclude B's `IndexedPhysicalCutStarUpperL` predicate. No additional assumption of no-(I2) or equality of selected/front graph-age F enters this elementary source-relation projection.

## Theorem B — bilateral live name cover gives exact projected spectrum equality

Assume `IndexedCutStarLiveCover A B c` and `IndexedCutStarLiveCover B A c`. Apply Theorem A in both directions. The two complete positive-cut upper ordinary-L spectra are equivalent for every R, even with differently sized finite indexed source universes, false E atoms or duplicated upper types.

## Theorem C — between two actual Henson AlgorithmRuns this is sufficient for full corrected (B3)

Let P,Q be two physical `HensonRunCutData` over the **same literal** E,k and source cut c, each with its own genuine original-prefix seed representation and full no-(I2) on its distinct pre-cut closure. The parent PR #174 constructs two exhaustive final Kpt-node indexes and Boolean presence masks `paramsP,liveP` and `paramsQ,liveQ`, each whose projected cut-star predicate equals the intrinsic physical cut-star of that run, and an implication `same indexed spectra → P.fullB3 iff Q.fullB3`.

Theorem B gives `same indexed spectra` from **two directional physical live name covers**, so we obtain:
```
∃ paramsP,liveP,paramsQ,liveQ,
  (each index exhaustive for the TRUE run's final closure)
  ∧ ((IndexedCutStarLiveCover Pidx Qidx c
     ∧ IndexedCutStarLiveCover Qidx Pidx c)
     → (P.fullB3 ↔ Q.fullB3)).
```
The cardinalities of the two index sets need not agree. Crucially, the two full-source exhaustiveness certificates and same-base old-L-socle comparison are DERIVED by the parent actual-run theorem, not assumed here.

## Adversarial checks (15)

1. The predicate quantifies over real physical Kpt-node index **j** with `live c j=true`, not arbitrary original-address labels, fake E-positive coordinates or unverified selected macrodiary vertices.
2. Both OLD and UPPER complete Kpt ancestor records must be `some` for the **same j**; live alone does not imply the node crosses c, and a terminal I1 node at c need not cross.
3. The positive cut test is an ordinary-`L` bit inside U.lReduct; E has no role in its truth.
4. U's entire next ordinary-`L` reduct is preserved, including all directed present AND ABSENT bits and singleton data; matching just the cut-edge is insufficient.
5. No matching of *off-cut* upper types is required. For Henson B3 this is justified by the **verified** anchor-free cut-star normal form, but structural I1/I2 and full envelope orbits may still need those off-cut types.
6. No matching of OLD dependent L+ types or auxiliary E bits is required for the B3 verdict; therefore this is weaker than the full physical L+ crossing-pair equality in Track E.
7. The relation is existential and may be many-to-one; no claimed preservation of index cardinality, multiplicity or injectivity.
8. Empty positive cut-star spectra work without inventing a source anchor. Matching hypotheses may be vacuous.
9. The source rank c is COMMON. Different target numerical gaps still require a real coordinate transport.
10. The two base E relations and generation k are literally shared by the `HensonRunCutData` type, so old-L-socle equality follows, but no claim that arbitrary refined diary occurrences can be represented over that one base without proof.
11. Genuine no-(I2) separately holds for each physical pre-cut closure when applying corrected B3; the indexed relation itself makes sense in the presence of forks.
12. The actual two-run theorem needs finite numerical H+ original-prefix seed representation, not just an arbitrary Kpt seed family.
13. Unknown upper–upper edges in a generic corrected-B3 L-only witness are never copied from either ambient.
14. The concrete K4 q2/x selected-shadow obstruction still applies: any genuine q2 positive physical cut-star upper type must be matched, even if q2 is not among the selected active diary branches.
15. The bilateral live-cover premise is a **new finite source matching target**, not an established property of all occurrences of the proposed canonical diary. No unconditional BRD, common labelled inverse-source monoid orbit or relative B3-loss bridge follows.

## Verification and merge gate

Commit this English audit first, then Lean. The parent branch #174 must complete its exact-head full kernel build with the expected **640** standard-only reports before merging. This stack adds three named theorem endpoints, targeting **643** reports on the combined tree if no concurrent Track G changes intervene. Require full `lake build`, parser self-test, no sorryAx/custom axioms. Do not alter black manuscript text or promote the global diary theorem.
