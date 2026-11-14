# Track D — the missing marked upper type occurs INSIDE the same failed full-(B3) clique
14 November 2026 — English proof and adversarial audit before Lean

## Precise improvement over earlier diagnostics

The already verified generic result
`selectedStagePool_fullB3_failure_has_extra_original` says that
when a marked source passes corrected B3 and a full source fails,
some FULL-selected actual original has a complete next-cut L-reduct
absent from the marked chosen-output profile. That result does not
assert that this missing source type appears in the specific forbidden
clique certifying the full B3 failure. The Track D exact physical-core
extraction provides one such clique and an actual physical name for
EVERY upper clique vertex, but does not distinguish which type is
missing from a particular marked source.

New theorem: given a genuine finite symmetric loop-free K_ell-free
numerical-H, ell≥2, ell≤k+1, a cut p<N, a finite actual original-name
map and TWO predicates Full,Marked on the same names, suppose:

* full selected-stage corrected B3 FAILS;
* marked selected-stage corrected B3 PASSES;
* some marked original w is ACTUALLY cut-eligible,
  p+1 ≤ A.freeLevel(original w).

Then there exist ONE bounded finite L-only model V and a single
K_ell clique e through p, with the true complete initial ordinary-L
socle through p, deletion of p avoiding the complete normalized
Henson family, and every upper V vertex lying in e's image. Moreover,
SOME UPPER CLIQUE VERTEX x=e(a)>p has ONE actual FULL original v with:

  Full(v);
  p+1≤A.freeLevel(original v);
  positive actual directed cut-edge A.L.binary p (original v) 0=true;
  PrefixType_V(p+1,x) = PrefixType_A.L(p+1,original v);
  NOT MarkedProfile.PrescribedUpperLType(
      (A.partialTypeAt(p+1,original v)).lReduct).

The last absence concerns the ACTUAL CHOSEN marked-output profile,
not merely the set of marked names and not only positive cut masks.

## Proof

Apply the checked
`henson_failed_selectedB3_has_exact_full_cut_star_core`
to the failing Full source. It produces V,e and, for every x>p
in V, a selected actual original v with ALL the eligibility,
cut-adjacency and COMPLETE L-type equalities. In particular e
contains p and V realizes K_ell, including at generation zero.

Let G be the marked selected-stage prescribed data. Because w is
marked AND eligible, the full old dependent L+ source type
T0=A.partialTypeAt p (original w) belongs to G.source. Its chosen
target G.target(T0) comes from SOME eligible marked physical original
u, which need NOT equal w. By the verified
selectedStagePoolPrescribedData_source_original and
ambient_partialType_prescribedSocle, G.target(T0) has exactly the
actual initial ordinary-L socle of A through p; V has the same
socle. Thus the common-socle premise of G.CorrectedB3 holds.

Suppose, for contradiction, that every upper clique vertex's
complete next-cut L-type belongs to G.PrescribedUpperLType.
Since the extracted V has no upper vertices except those of the
same clique, ALL upper V vertices have permitted marked types.
The marked corrected B3 test, applied to source T0 and finite V,
now forces V to avoid the normalized forbidden K_ell family:
V has the right old socle, genuine finite carrier, prescribed
upper L-types, and V.withoutVertex p avoids the family.
But V realizes the forbidden K_ell via e. Contradiction.

Hence one upper clique vertex x=e(a)>p has a type NOT permitted
by G. The physical original v assigned to this SAME x in the
checked full-core extraction has all the listed properties.
Because equality is of COMPLETE next-cut L-prefix types,
membership/nonmembership in the chosen marked source family
transfers to the physical v's next ordinary L-reduct using
partialTypeAt_lReduct_eq_ofAgeModel.

No no-(I2) premise is required! We never infer that being
physically marked implies chosen-output membership; instead we
derive an actual chosen-output MISSING TYPE from the marked B3
test. This is strictly weaker and robust even at (I2) cuts.

## 17 adversarial checks

1. The marked source must contain a *cut-eligible* selected original,
   not merely an index declared marked.
2. The marked profile's actual chosen target may be represented by
   u≠w, so prove equality of lower L-socles from the actual chosen
   u rather than assuming G.target(T0)=A.nextType(w).
3. The relative common socle includes ALL directed negative
   old L atoms and the carrier, not just positive graph edges.
4. Compare physical v with the specific upper x=e(a), not with a
   second arbitrary abstract permitted type.
5. Carry cut-eligibility AND actual positive L cut-adjacency for the
   SAME v.
6. The missing type is COMPLETE next directed L-reduct including
   all old-to-upper and upper-to-old relations, not a support mask.
7. Do not assume that all full physical source names are marked or
   that the marked B3 test is equivalent to the full B3 test.
8. The forbidden continuation V is an arbitrary L-only age model,
   with upper-upper edges unconstrained by actual H.
9. No auxiliary E is assigned to V.
10. The normalized forbidden family contains loops and asymmetric
    patterns; the genuine finite Henson clique-core theorem was
    proved with these excluded, INCLUDING generation zero.
11. Every upper V vertex comes from ONE clique; without this,
    a nonclique upper type could be the missing source and the
    conclusion would not follow.
12. The omitted marked upper type could belong to an AUXILIARY
    Kpt parameter (e.g. K4 q2), even when the selected active
    diary age stays unchanged.
13. No no-(I2) hypothesis is needed for THIS missing-type
    extraction. It would become necessary if one tried to infer
    chosen-target inclusion from marked name membership.
14. No sorting/weight w of upper vertices into selected active
    diary sorts has yet been constructed.
15. Hence this does NOT prove the full B3-loss ↔ relative graph-age
    loss bridge, nor common labelled source orbit.
16. Keep the global manuscript Lemma Kk_Boring_Level pending.
    No frozen black TeX or old validation marks change.
17. The theorem and exact named standard-only transitive-axiom
    report must pass a genuine hosted Lean compilation before
    any new olive statement is described as verified.

## Lean module contract

Import the previously validated exact finite cut-star witness,
the already checked same-ambient socle/marked-source bridge,
and the cross-ambient SameInitialL reversal.
Prove the result at one finite Henson cut by contradiction.
Do not alter old proof bodies or central registry while parallel
other tracks are still merging. Register one isolated exact-head
theorem and full-project CI gate first.
