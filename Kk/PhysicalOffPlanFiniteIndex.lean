import Kk.PhysicalBareFiniteOldRangeStability
import Kk.CrossHeightPlannedCutCover
import Mathlib.Tactic

/-!
# Track E: physically indexed finite no-unplanned-cut certificate

Two independently exhaustive genuine Kpt source indices are enough
to check the no-novelty criterion ONLY at old-boring off-plan cuts.
Combining this with the REAL bare-original numerical-H+ construction
gives a height-filtered physical ALLOWED-CUT sandwich.

The actual resolved diary must still produce the finite matching
predicate; it is not inferred from old ordinary graph columns.

English-first proof and hostile audit:
  docs/track_e_physical_indexed_offplan_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two finite source indices certify only the old-boring OFF-PLAN cuts.
The sources may have different sizes, and all full old/upper L+ pairs
are matched with one OLD Kpt source node, preserving I2 forks.
Neither source-label transport nor equality of outgoing monoid maps
is part of this predicate. -/
def KptTwoIndexOffPlanNoNovelty
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat) (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool) : Prop :=
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
    ∀ j : Fin Q, newLive cut j = true →
      LevelTree.lev (newNode j) = cut →
      ∃ i : Fin P, oldLive cut i = true ∧
        LevelTree.lev (oldNode i) = cut) ∧
  (∀ cut : Nat, cut < oldTop →
    cut ∉ oldSelected cut → cut ∉ Allowed →
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

/-- From two EXACT actual Kpt source indices and their off-plan
finite terminal/full-L+ pair tests, derive the physically correct
height-filtered allowed-cut selected-level sandwich.

The finite test is only assumed at cuts outside Allowed which the
old genuine run skips. This is strictly weaker than asking for
no-novelty at every old-range cut. -/
theorem crossheight_old_range_sandwich_of_two_finite_offplan_indices
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ a : Fin P, oldNode a = z ∧ oldLive cut a = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y ↔
        ∃ a : Fin Q, newNode a = z ∧ newLive cut a = true)
    (hFinite : KptTwoIndexOffPlanNoNovelty family RunOld.I oldTop
      Allowed oldNode newNode oldLive newLive) :
    ∀ i : Nat, i ≤ oldTop →
      (RunOld.I i ⊆ RunNew.I i) ∧
      ({q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} ⊆
        RunOld.I i ∪ {q : Nat | q ∈ Allowed ∧ i ≤ q}) := by
  apply crossheight_old_range_sandwich_of_offplan_no_novelty
    family X Y hXY oldTop newTop hTopLe hTopSeed
    RunOld RunNew Allowed
  intro cut hCut hOldSkip hOffPlan
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunOld.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunNew.I (cut+1)) Y
  constructor
  · rintro ⟨z,hNewZ,hLevel⟩
    obtain ⟨j,hNode,hLive⟩ := (hExactNew cut hCut z).mp hNewZ
    obtain ⟨a,hOldLive,hOldLevel⟩ :=
      hFinite.1 cut hCut hOldSkip hOffPlan
        j hLive (by simpa only [hNode] using hLevel)
    exact ⟨oldNode a,
      (hExactOld cut hCut (oldNode a)).mpr
        ⟨a,rfl,hOldLive⟩,hOldLevel⟩
  · intro p hp
    have hNewIndexed :
        p ∈ IndexedPhysicalCrossing family newNode newLive cut := by
      rw [indexed_physical_crossing_eq_full_closure_relation
        family newNode newLive ZY cut (hExactNew cut hCut)]
      exact hp
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hNewIndexed
    obtain ⟨a,hOldLive,hOldType,hUpperType⟩ :=
      hFinite.2 cut hCut hOldSkip hOffPlan
        j hLive p.1 p.2 hOldRaw hUpperRaw
    have hOldIndexed :
        p ∈ IndexedPhysicalCrossing family oldNode oldLive cut :=
      ⟨a,hOldLive,hOldType,hUpperType⟩
    rw [indexed_physical_crossing_eq_full_closure_relation
      family oldNode oldLive ZX cut (hExactOld cut hCut)] at hOldIndexed
    exact hOldIndexed

/-- The numerical-H+ physical application: from one actual OLD
exhaustive Kpt run, true old-block fidelity, both K-free physical
structures and one NEW genuine original, CONSTRUCT both exhaustive
finite source indices. If their concrete OFF-PLAN tests pass, the
new bare-root run has NO unexpected selected old-range level.

This is conditional: it does not infer the finite tests from any
particular resolved diary or establish a labelled source orbit. -/
theorem finiteNumericH_bareTopRoot_sandwich_of_finite_offplan_coverage
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
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop)
    (Allowed : Set Nat) :
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
              (KptTwoIndexOffPlanNoNovelty family RunOld.I
                oldTop Allowed
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
    exact crossheight_old_range_sandwich_of_two_finite_offplan_indices
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
