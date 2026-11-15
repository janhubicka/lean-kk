import Kk.PhysicalBareFiniteOldRangeStability
import Kk.CrossHeightPlannedCutCover
import Mathlib.Tactic

/-!
# Track G: physical *off-plan* finite source certificates

For a growing-height actual Kpt run, complete old/upper dependent L+
source coverage is needed ONLY at cuts that were boring in the old run
and are not explicitly permitted by the refined resolved diary.

The two source indices are separately exhaustive; their cardinalities
need not agree. The actual bare-original new-root run is constructed
from physical numerical H+ inputs, with all safe-column/avoidance
hypotheses retained, NOT from the abstract diary age.

English proof and adversarial checklist written first:
docs/track_g_physical_offplan_finite_certificate_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Finite NEW-to-OLD source checks only at old-boring, disallowed cuts.
The terminal check is existence-only; the crossing check uses a SINGLE
old live index for BOTH complete dependent L+ raw ancestor types.
The old/new index sets and their cardinalities are independent. -/
def KptTwoIndexOffPlanNoNovelty
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldTop : Nat)
    (oldSelected : Nat → Set Nat)
    (Allowed : Set Nat)
    (nodeX : Fin P → AdmissibleKptNode family)
    (nodeY : Fin Q → AdmissibleKptNode family)
    (liveX : Nat → Fin P → Bool)
    (liveY : Nat → Fin Q → Bool) : Prop :=
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
    ∀ j : Fin Q, liveY cut j = true →
      LevelTree.lev (nodeY j) = cut →
      ∃ i : Fin P, liveX cut i = true ∧
        LevelTree.lev (nodeX i) = cut) ∧
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
    ∀ j : Fin Q, liveY cut j = true →
      ∀ T : PartialTypeWithE cut db du dd,
        ∀ U : PartialTypeWithE (cut+1) db du dd,
          kptFullOldAtCut (nodeY j) cut =
            some (⟨cut,T⟩ : RawPartialTypeNode db du dd) →
          kptFullUpperAtCut (nodeY j) cut =
            some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) →
          ∃ i : Fin P, liveX cut i = true ∧
            kptFullOldAtCut (nodeX i) cut =
              some (⟨cut,T⟩ : RawPartialTypeNode db du dd) ∧
            kptFullUpperAtCut (nodeX i) cut =
              some (⟨cut+1,U⟩ : RawPartialTypeNode db du dd))

/-- A finite-index sufficient condition for the source-level
old-range *sandwich*. Unlike the older all-cut no-novelty gate,
nothing is required at already-interesting or explicitly allowed
cuts. This does not prove that allowed cuts actually occur. -/
theorem crossheight_runs_old_range_sandwich_of_two_finite_offplan_cover
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (oldTop newTop : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (nodeX : Fin P → AdmissibleKptNode family)
    (nodeY : Fin Q → AdmissibleKptNode family)
    (liveX : Nat → Fin P → Bool)
    (liveY : Nat → Fin Q → Bool)
    (hExactX : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, nodeX i = z ∧ liveX cut i = true)
    (hExactY : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y ↔
        ∃ j : Fin Q, nodeY j = z ∧ liveY cut j = true)
    (hOffPlan : KptTwoIndexOffPlanNoNovelty family oldTop
      RunOld.I Allowed nodeX nodeY liveX liveY) :
    ∀ i : Nat, i ≤ oldTop →
      (RunOld.I i ⊆ RunNew.I i) ∧
      ({q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} ⊆
        RunOld.I i ∪ {q : Nat | q ∈ Allowed ∧ i ≤ q}) := by
  classical
  apply crossheight_old_range_sandwich_of_offplan_no_novelty
    family X Y hXY oldTop newTop hTopLe hTopSeed
    RunOld RunNew Allowed
  intro cut hCut hOldBoring hNotAllowed
  constructor
  · rintro ⟨z,hZY,hLev⟩
    obtain ⟨j,hNode,hLive⟩ := (hExactY cut hCut z).mp hZY
    obtain ⟨i,hOldLive,hOldLevel⟩ :=
      hOffPlan.1 cut hCut hOldBoring hNotAllowed j hLive
        (by simpa only [hNode] using hLev)
    exact ⟨nodeX i, (hExactX cut hCut (nodeX i)).mpr
      ⟨i,rfl,hOldLive⟩, hOldLevel⟩
  · intro p hp
    have hNewIndexed :
        p ∈ IndexedPhysicalCrossing family nodeY liveY cut := by
      rw [indexed_physical_crossing_eq_full_closure_relation
        family nodeY liveY
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y) cut (hExactY cut hCut)]
      exact hp
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hNewIndexed
    obtain ⟨i,hOldLive,hOldType,hUpperType⟩ :=
      hOffPlan.2 cut hCut hOldBoring hNotAllowed
        j hLive p.1 p.2 hOldRaw hUpperRaw
    have hOldIndexed :
        p ∈ IndexedPhysicalCrossing family nodeX liveX cut :=
      ⟨i,hOldLive,hOldType,hUpperType⟩
    rw [indexed_physical_crossing_eq_full_closure_relation
      family nodeX liveX
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X) cut (hExactX cut hCut)] at hOldIndexed
    exact hOldIndexed

/-- CONSTRUCT both genuine physical bare-root AlgorithmRuns and
their independently exhaustive finite live source indices. The only
remaining comparison hypothesis is the explicitly OFF-PLAN finite
terminal/pair cover, not all-cut no-novelty.

No common labelled source orbit, uniform envelope carrier, or infinite
Henson resolved-copy schedule is established here. -/
theorem finiteNumericH_bareTopRoot_old_range_offplan_sandwich
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
    (Allowed : Set Nat)
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
              (KptTwoIndexOffPlanNoNovelty family oldTop
                RunOld.I Allowed
                (fun a : Fin oldParams.card =>
                  (oldParams.equivFin.symm a).val)
                (fun a : Fin newParams.card =>
                  (newParams.equivFin.symm a).val)
                oldLive newLive →
                ∀ i : Nat, i ≤ oldTop →
                  (RunOld.I i ⊆ RunNew.I i) ∧
                  ({q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} ⊆
                    RunOld.I i ∪ {q : Nat | q ∈ Allowed ∧ i ≤ q})) := by
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
    exact crossheight_runs_old_range_sandwich_of_two_finite_offplan_cover
      family X Y hXY oldTop newTop hTopLe hOldTopSeed
      RunOld RunNew Allowed
      (fun a : Fin oldParams.card =>
        (oldParams.equivFin.symm a).val)
      (fun a : Fin newParams.card =>
        (newParams.equivFin.symm a).val)
      oldLive newLive hOldExact
      (fun cut hc z => hNewExact cut
        (lt_of_lt_of_le hc hTopLe) z)
      hFinite i hi

end Kk
