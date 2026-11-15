import Kk.PhysicalBareNewRootRun
import Kk.CrossHeightFiniteIndexStability
import Mathlib.Tactic

/-!
# Track E: genuine bare-root finite certificates for old-range stability

This is the next physical application of the checked bare-original-only
new-root construction. The new actual physical run is constructed without
choosing any old generating parameter set I: the old-closure-plus-root
source is used only as an auxiliary bound/cover in the previous theorem.

With an existing true old exhaustive run, the result produces two
independent complete finite node indices. If their concrete, one-sided
terminal and *full dependent L+ crossing pair* coverage tests pass,
the old-range selected-level sets of the two true runs agree after
height restriction. This deliberately proves no common labelled orbit.

English-first adversarial audit:
  docs/track_e_physical_bare_finite_oldrange_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The true bare-root numerical H+ source produces an ACTUAL complete
physical exhaustive run. There is no inherited-parameter-set argument:
instantiate the previously verified bounded bare-run constructor with
I=∅. This is only a representation/cover device, not an inserted seed. -/
theorem finiteNumericH_bareTopRoot_has_physical_exhaustive_run
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U) :
    HasPhysicalExhaustiveKptRun family
      (finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X)
      (hPosition k (j-1) k+1) := by
  classical
  obtain ⟨_hBound,Run,hTop,params,live,hParams,hInj,hPresent,hCover⟩ :=
    finiteNumericH_bareTopRoot_construct_exhaustive_run
      family K L k b N M j hNM hBlock hk hj
      hTarget hNTop hBin hUn hDiag hAvoidK hAvoidL
      U X hSeeds (∅ : Set Nat)
  exact ⟨Run,hTop,params,live,hParams,hInj,hPresent,hCover⟩

/-- The entirely finite NEW-to-OLD no-novelty test at all old-range
cuts. The two node-index types can have different cardinalities.

The terminal test compares existence at the cut, not identities.
The pair test compares complete old/upper dependent L+ raw types
from the SAME live node, including auxiliary E and I2 forks.
Neither test asserts correspondence of full labelled source records. -/
def KptTwoIndexOldRangeNoNovelty
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldTop : Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) : Prop :=
  (∀ cut : Nat, cut < oldTop →
    ∀ j : Fin Q, newLive cut j = true →
      LevelTree.lev (newNode j) = cut →
      ∃ i : Fin P, oldLive cut i = true ∧
        LevelTree.lev (oldNode i) = cut) ∧
  (∀ cut : Nat, cut < oldTop →
    ∀ j : Fin Q, newLive cut j = true →
      ∀ T : PartialTypeWithE cut db du dd,
        ∀ U : PartialTypeWithE (cut+1) db du dd,
          kptFullOldAtCut (newNode j) cut =
            some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
          kptFullUpperAtCut (newNode j) cut =
            some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
          ∃ i : Fin P, oldLive cut i = true ∧
            kptFullOldAtCut (oldNode i) cut =
              some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
            kptFullUpperAtCut (oldNode i) cut =
              some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd))

/-- For an actual old exhaustive numerical-H+ Kpt run, physically
CONSTRUCT the new *bare original-only* run and BOTH independent
exhaustive finite indices. If their concrete full-L+ finite
NEW→OLD coverage predicate passes, then selected levels of the
real higher run restricted to the old horizon equal the old levels
at every stage.

The no-novelty predicate is NOT inferred from old-column agreement:
certifying it from synchronized resolved diaries is still the open
geometric obligation. No inverse-source maps or uniform BRD bound
are asserted. -/
theorem finiteNumericH_bareTopRoot_old_range_stable_of_two_finite_covers
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    ∃ RunOld : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ RunNew : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family)
        (finiteNumericH_bareTopRootSeeds
          family L k M j hAvoidL hTarget X)
        (hPosition k (j-1) k+1),
      ∃ oldParams : Finset (AdmissibleKptNode family),
        ∃ oldLive : Nat → Fin oldParams.card → Bool,
          ∃ newParams : Finset (AdmissibleKptNode family),
            ∃ newLive : Nat → Fin newParams.card → Bool,
              (∀ cut : Nat, cut < oldTop →
                ∀ z : AdmissibleKptNode family,
                  z ∈ SMTree.Envelope.closure
                    (admissibleKptSTree family)
                    (RunOld.I (cut+1)) X ↔
                  ∃ a : Fin oldParams.card,
                    (oldParams.equivFin.symm a).val = z ∧
                    oldLive cut a = true) ∧
              (∀ cut : Nat, cut < oldTop →
                ∀ z : AdmissibleKptNode family,
                  z ∈ SMTree.Envelope.closure
                    (admissibleKptSTree family)
                    (RunNew.I (cut+1))
                    (finiteNumericH_bareTopRootSeeds
                      family L k M j hAvoidL hTarget X) ↔
                  ∃ a : Fin newParams.card,
                    (newParams.equivFin.symm a).val = z ∧
                    newLive cut a = true) ∧
              (KptTwoIndexOldRangeNoNovelty family oldTop
                (fun a : Fin oldParams.card =>
                  (oldParams.equivFin.symm a).val)
                (fun a : Fin newParams.card =>
                  (newParams.equivFin.symm a).val)
                oldLive newLive →
                ∀ i : Nat, i ≤ oldTop →
                  RunOld.I i =
                    {q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop}) := by
  classical
  obtain ⟨RunOld,hOldTopSeed,oldParams,oldLive,
    _hOldAll,_hOldInj,_hOldPresent,hOldExact⟩ := hOldPhysical
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  let newTop : Nat := hPosition k (j-1) k+1
  have hNewPhysical : HasPhysicalExhaustiveKptRun family Y newTop :=
    finiteNumericH_bareTopRoot_has_physical_exhaustive_run
      family K L k b N M j hNM hBlock hk hj
      hTarget hNTop hBin hUn hDiag hAvoidK hAvoidL U X hSeeds
  obtain ⟨RunNew,_hNewTopSeed,newParams,newLive,
    _hNewAll,_hNewInj,_hNewPresent,hNewExact⟩ := hNewPhysical
  have hTopLe : oldTop ≤ newTop :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  have hXY : X ⊆ Y := by
    intro z hz
    exact Or.inl hz
  refine ⟨RunOld,RunNew,oldParams,oldLive,
    newParams,newLive,?_,?_,?_⟩
  · exact hOldExact
  · intro cut hc z
    exact hNewExact cut (lt_of_lt_of_le hc hTopLe) z
  · intro hFinite i hi
    exact crossheight_runs_old_range_eq_of_two_finite_index_cover
      family X Y hXY oldTop newTop hTopLe hOldTopSeed
      RunOld RunNew
      (fun a : Fin oldParams.card =>
        (oldParams.equivFin.symm a).val)
      (fun a : Fin newParams.card =>
        (newParams.equivFin.symm a).val)
      oldLive newLive hOldExact
      (fun cut hc z => hNewExact cut
        (lt_of_lt_of_le hc hTopLe) z)
      hFinite.1 hFinite.2 i hi

end Kk
