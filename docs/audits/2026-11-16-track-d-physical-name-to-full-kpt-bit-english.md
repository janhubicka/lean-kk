# Track D — transport a concrete old-generation-zero original separator into the FULL Kpt node index
16 November 2026. English proof and hostile audit BEFORE Lean.

## Verified vs stacked dependencies

This is STACKED on draft [Track D PR #268](https://github.com/janhubicka/lean-kk/pull/268), defining `KptOldOrdinaryBitSeparation` as one earlier ordinary-L bit that differs in the COMPLETE dependent old L+ records of TWO genuine Kpt nodes. This new source is NOT independently mergeable while its predecessor has not passed exact-head dedicated checks.

Independently merged and verified [PR #264](https://github.com/janhubicka/lean-kk/pull/264) proves `finiteNumericH_old_zero_separates_top_from_negative`, including:
- one genuine old Q original base `old < cutBase`;
- one later selected TOP coding base `selected>cutBase` with base E(old,selected)=true;
- one later negative auxiliary base `aux>cutBase` with E(old,aux)=false and arbitrary generation m≤k;
- a tested real numerical cut `c=hPosition k cutBase g` with g≤k;
- a PHYSICAL generation-zero old coordinate `old0=hPosition k old 0` with `old0<c`, positive old-to-selectedTop L and negative old-to-auxCopy L bits; and complete physical old type distinction.

The new theorem connects these two pieces WITHOUT falsely assuming that any full Kpt source node representing a given physical upper original exists in the specific pre-cut closure.

## Precise theorem

Fix a base E:Nat×Nat→Bool and physical numerical H(E,k,N), old<cutBase<selected and old<cutBase<aux, g,m≤k, E(old,selected)=true, E(old,aux)=false. Fix an ACTUAL physical cut `c=hPosition k cutBase g<N` and actual named original addresses
`selectedName auxName : Fin N`
with
`selectedName.val = hPosition k selected k` and
`auxName.val = hPosition k aux m`.

Fix a genuine Henson (or arbitrary binary normalized) Kpt family and two actual admissible nodes `zS,zA : AdmissibleKptNode family`. **Assume the exact dependent old-type source representation**, not just one ordinary passing bit:
`kptFullOldAtCut zS c = some ⟨c, A.partialTypeAt c selectedName.val⟩`,
`kptFullOldAtCut zA c = some ⟨c, A.partialTypeAt c auxName.val⟩`,
where A is the TRUE finite numerical H+ partial structure.

Then `KptOldOrdinaryBitSeparation zS zA c` holds, with one explicitly named old coordinate `old0=hPosition k old 0<c`, namely:
`(A.partialTypeAt c selectedName).lReduct.binary (some old0) none 0 = true`, while the analogous bit for auxName equals false.

Consequently the two **actual Kpt node** full old dependent records are unequal. Thus this pair CANNOT witness I2 at the cut, regardless of their next-cut upper types.

## Proof

1. Apply checked physical generation-zero separator to `E,k,N,old,cutBase,selected,aux,g,m`, obtaining `old0<c`, exact positive old-to-selectedTop and negative old-to-auxCopy L bits. The numeric table lemma does not itself guarantee target membership; the two supplied names `selectedName,auxName : Fin N` and address equalities guarantee that.
2. For A, define the two actual dependent old types T and U from `A.partialTypeAt c` of those finite names. By the checked `partialTypeAt_lReduct_eq_ofAgeModel`, T.lReduct is EXACTLY the ordinary prefix-L reduct from `A.L` at the selectedName original, and similarly for U.
3. Evaluate their ordinary binary atoms at `(some (⟨old0,hOldBelow⟩ : Fin c), none, 0)`. The physical bit identities and supplied name address equalities give true vs false.
4. Use the **two explicit exact old full-source representation assumptions** to conclude the proposed `KptOldOrdinaryBitSeparation zS zA c`. Apply the checked generic separator⇒full-old-distinct theorem from the predecessor if a second result is desired; it is not necessary for the witness construction itself.

No graph-age capacity, source orbit, selected-shadow cover, or free E on an arbitrary L-only age-test witness is smuggled into the argument.

## Adversarial checks

1. The full source is TWO actual Kpt nodes `zS,zA`, not two abstract typed future vertices in an arbitrary L-only age witness.
2. Their old raw Kpt records are `Option (RawPartialTypeNode)`; demanding EXACT `some ⟨c, A.partialTypeAt c name⟩` is crucial. Without it a physical graph bit does not distinguish arbitrary generated meet nodes.
3. The numerical-H binary table is total on Nat; `selectedName auxName : Fin N` and `c<N` make the targets genuine named finite originals.
4. The proof's old separator `old0` is below c. Since c<N, it also lies within the physical finite carrier.
5. The positive selected target has TOP generation k. It may be selected only in the intended Q application, not in this generic finite lemma.
6. The negative target is a LATER original base at ANY m≤k. Its base ordinary-L nonedge is retained at every generation gate, including the special top/top case.
7. The same concrete coordinate old0 supplies the two ordinary L bits; a different witness for each target would not establish type inequality.
8. Complete dependent old L+ records include auxiliary E; different ordinary L reduct bits suffice for inequality but do not imply any E equality.
9. No no-I1/no-I2 premise is needed for this pairwise separation; it is an input that can help prove no-I2 after checking all active pairs.
10. No source membership `zS,zA∈closure(R.I(c+1),X)` is derived. This belongs to the actual full-source instantiation.
11. There may exist other active generated nodes with unequal next types; separating THIS pair alone does not exclude all I2.
12. The older canonical singleton≤2 implies old neighbour lemma [PR #263](https://github.com/janhubicka/lean-kk/pull/263) is distinct: it produces the old base `old` only under the actual finite old-column reference-age hypotheses. The present theorem ASSUMES the base old and its two directed E(old,target) bits.
13. The base graph E may be arbitrary in this physical bit computation; K_ell-freeness enters only when constructing actual Henson valid sources elsewhere.
14. The cut c is real at generation g≤k and strictly below its later physical target positions; do not relabel c as an arbitrary compressed Kpt level.
15. The `lReduct` comparison includes directed ordinary atoms and negative values; do not substitute a single selected graph-age number.
16. A proof using `PartialTypeWithE` raw representation must respect the dependent cut length exactly. Any attempted cast must be justified, not hidden by `sorry`.
17. The predecessor PR #268 is still a *draft* and is not certified by a general Lean gate that does not import the module. This stacked PR requires its own direct build and standard-only exact axiom gate.
18. The manuscript's independent-set upper and common labelled inverse source remain pending until all Q base/source pair types and structural I1/I2 events are handled.

## Lean file

`Kk/K4PhysicalOldBitToKptCertificate.lean` imports the predecessor `Kk/FullKptOldLBitNoFork.lean` and checked `Kk/K4GenerationZeroSourceSeparator.lean`. State `kpt_old_ordinary_bit_certificate_of_named_numeric_originals` with the TWO exact raw old source equations. Prove the explicit finite old coordinate witness by checked H literal gate and `partialTypeAt_lReduct_eq_ofAgeModel`. Also state the immediate resulting raw-old unequal corollary. Register BOTH names in a dedicated direct exact-head strict gate.

This is a component toward the all-index I2 certificate, not a claim that a specific arbitrary pair of generated source nodes is represented by these two physical originals.
