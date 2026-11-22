import Kk.TrackCSmallBareRootExceptionBudget
import Kk.TrackCOldRangeNoNewRootFreeEnd
import Mathlib.Tactic

/-!
# Track C: genuine chronological one-root old-range E-free exception budget

English FIRST and 28 hostile checks:
 docs/track_c_chronological_oldrange_optimal_audit_20261122.md

This combines the independently verified FULL-dependent bare-root physical
source transport with the actual old-range exception filtration.

One old finite physical original pool U, one TRUE old AlgorithmRun
Rold on literal Kpt seeds X, and one actual higher chronological
new ORIGINAL w suffice to construct the exact small new original pool
W=Fin.castLE[U]∪{w} and ONE physically genuine exceptional odd-support
set of old-range source cuts F. Its cardinal is bounded by
   |F| <= |U| + |the ACTUALLY selected old Kpt source levels Rold.I0|,
independent of numeric M and boring-gap lengths and WITHOUT charging
the new root w, which ends at or above oldTop.

Every old-unselected odd cut outside F is FULL candidate quiet provided
the COMPLETE old dependent Kpt prefix witnesses of active original
representatives are supplied. This does NOT derive those witnesses
from a resolved diary, handle exceptional cuts or nonzero real cuts,
compare physically taller new runs, or prove global BRDs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Genuine finite K/L chronological one-root extension:
the finite set F of COMPLETE physical original auxiliary E-free ends
STRICTLY below oldTop costs at most the inherited OLD root-original
cardinality plus the ACTUAL old selected Kpt levels, with NO +1.

The initial new source is exactly the BARE X union one physical
original O_w; the old complete Kpt seed representation is transported
from old K into new L, including all directed E and negative L atoms.
One true old AlgorithmRun is constructed from the supplied physical
exhaustive-run certificate; its genuine selected-tail is used.

At odd old-unselected source cuts outside F, full candidate no-novelty
is conditional on COMPLETE OLD Kpt prefix witnesses of all active
original representatives, as in the verified Track C odd theorem.
No global diary-uniform source count or bigger-height synchronization. -/
theorem finiteNumericH_constructed_odd_quiet_outside_oldrange_root_budget
    (family : List (NormalizedForbidden 1 0 1))
    (K L : AgeTestModel 1 0 1)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin 1, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin 0,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin 1,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSymL : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK (U : Set (Fin N)))
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let w : Fin M := ⟨hPosition k j k, hTarget⟩
    let W : Finset (Fin M) := U.image (Fin.castLE hNM) ∪ {w}
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ F : Finset Nat,
        Y ⊆ ambientPrefixPool family
          (finiteNumericH L k M) hAvoidL (W : Set (Fin M)) ∧
        W.card ≤ U.card+1 ∧
        F.card ≤ U.card +
          (kpt_old_actual_selected_levels family X oldTop Rold).card ∧
        (∀ cut : Nat, cut ∈ F → cut < oldTop) ∧
        ∀ a : Nat,
          2*a+1 < oldTop →
          2*a+1 ∉ Rold.I (2*a+1) →
          2*a+1 ∉ F →
          KptCandidateOriginalOldPrefixCovered
            family L k M hAvoidL W X Y oldTop Rold (2*a+1) →
          NewRootNoNoveltyAtCut family
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I ((2*a+1)+1)) X)
            (SMTree.Envelope.closure (admissibleKptSTree family)
              (Rold.I ((2*a+1)+1)) Y)
            (2*a+1) := by
  classical
  let B : EnumeratedPartialStructure 1 0 1 := finiteNumericH L k M
  let w : Fin M := ⟨hPosition k j k, hTarget⟩
  let U' : Finset (Fin M) := U.image (Fin.castLE hNM)
  let W : Finset (Fin M) := U' ∪ {w}
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold,hOldTopSeed,_oldParams,_oldLive,
    _oldFinal,_oldInj,_oldPresent,_oldExact⟩ := hOldPhysical
  have hOldLift :
      X ⊆ ambientPrefixPool family B hAvoidL
        ((Fin.castLE hNM) '' (U : Set (Fin N))) :=
    finiteNumericH_baseExtension_old_seedPool_lifts
      family K L k b N M hNM hBlock hBin hUn hDiag
      hAvoidK hAvoidL (U : Set (Fin N)) X hSeeds
  have hOldRootSub :
      ((Fin.castLE hNM) '' (U : Set (Fin N))) ⊆
        (W : Set (Fin M)) := by
    rintro v ⟨u,hu,rfl⟩
    change Fin.castLE hNM u ∈ W
    change Fin.castLE hNM u ∈ U' ∪ ({w} : Finset (Fin M))
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hw : w ∈ (W : Set (Fin M)) := by
    change w ∈ W
    simp [W]
  have hBare :
      Y = X ∪
        ({B.kptOriginal family hAvoidL w} :
          Set (AdmissibleKptNode family)) := by
    change X ∪
      ((fun v : Fin M => B.kptOriginal family hAvoidL v) ''
        ({w} : Set (Fin M))) = _
    simp only [Set.image_singleton]
  have hCover : Y ⊆
      ambientPrefixPool family B hAvoidL (W : Set (Fin M)) := by
    intro z hz
    rw [hBare] at hz
    rcases hz with hzOld | hzNew
    · obtain ⟨o,⟨v,hv,ho⟩,hBelow⟩ := hOldLift hzOld
      exact ⟨o,⟨v,hOldRootSub hv,ho⟩,hBelow⟩
    · have hzEq : z = B.kptOriginal family hAvoidL w :=
        Set.mem_singleton_iff.mp hzNew
      subst z
      exact ⟨B.kptOriginal family hAvoidL w,
        ⟨w,hw,rfl⟩,le_rfl⟩
  have hUCard : U'.card ≤ U.card := Finset.card_image_le
  have hWCard : W.card ≤ U.card+1 := by
    calc
      W.card = (U' ∪ {w}).card := rfl
      _ ≤ U'.card + ({w} : Finset (Fin M)).card :=
        Finset.card_union_le U' ({w} : Finset (Fin M))
      _ = U'.card + 1 := by simp
      _ ≤ U.card + 1 := Nat.add_le_add_right hUCard 1
  have hOldTopLe : oldTop ≤ hPosition k (j-1) k+1 :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK
      (U : Set (Fin N)) X hSeeds hOldTopSeed
  have hNewFree : B.freeLevel w.val =
      hPosition k (j-1) k+1 :=
    finiteNumericH_top_freeLevel_exact L k M j hk hj hTarget
  have hNewAbove : oldTop ≤ B.freeLevel w.val := by
    rw [hNewFree]
    exact hOldTopLe
  let F : Finset Nat :=
    KptPhysicalOldRangeStageFreeEnds
      family L k M U' w X oldTop Rold
  have hFCount :
      F.card ≤ U'.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card :=
    kpt_physical_oldrange_freeends_card_le_roots_add_selected
      family L k M U' w X oldTop Rold hNewAbove
  have hFBound :
      F.card ≤ U.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card := by
    omega
  have hFRange : ∀ cut : Nat, cut ∈ F → cut < oldTop := by
    intro cut hCut
    exact ((mem_KptPhysicalOldRangeStageFreeEnds_iff
      family L k M U' w X oldTop Rold cut).mp hCut).2
  refine ⟨Rold,F,hCover,hWCard,hFBound,hFRange,?_⟩
  intro a hCut hUnselected hNotF hPrefix
  let c : Nat := 2*a+1
  have hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) X) c := by
    intro hInteresting
    have hStep := (Rold.interesting_step c hCut hInteresting).1
    apply hUnselected
    rw [hStep]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hRootNe : B.freeLevel w.val ≠ c := by
    omega
  have hNotFull :
      c ∉ KptPhysicalFinalStageFreeEnds
        family L k M W X oldTop Rold := by
    intro hc
    have hInF : c ∈ F :=
      (mem_KptPhysicalOldRangeStageFreeEnds_iff
        family L k M U' w X oldTop Rold c).mpr ⟨hc,hCut⟩
    exact hNotF hInF
  have hNoEnd :
      ∀ v : Fin M,
        v ∈ ambientStagePool B
          (W : Set (Fin M)) (Rold.I (c+1)) →
        B.freeLevel v.val ≠ c :=
    kpt_physical_no_stage_free_end_outside_final
      family L k M W X oldTop Rold c hCut hNotFull
  exact finiteNumericH_old_boring_one_bare_odd_noNovelty_general
    family L k M hAvoidL hSymL W X Y hCover
    w hBare oldTop Rold a hBoring hRootNe hNoEnd hPrefix

end Kk

#check @Kk.finiteNumericH_constructed_odd_quiet_outside_oldrange_root_budget
#print axioms Kk.finiteNumericH_constructed_odd_quiet_outside_oldrange_root_budget
