import Kk.TrackCOddSelectedLevelExceptionBudget
import Mathlib.Tactic

/-!
# Track C: old-range physical E-free endpoints do NOT charge the later new root

English FIRST, adversarial audit in:
 docs/track_c_oldrange_new_root_freeend_removed_audit_20261122.md

Let the genuine complete physical stage use initial root originals
U∪{w} and a TRUE old normalized Kpt AlgorithmRun R. If the new root
w has its literal auxiliary E-free endpoint at or ABOVE oldTop,
then all endpoints STRICTLY BELOW oldTop already come from the
stage based on U alone. Track E E86 bounds that stage by the
number of inherited physical original roots plus the number of
ACTUALLY selected old levels.

This is an exact finite old-range physical exception bound with
NO +1 new-root contribution. It does not show a cut is quiet
without complete old Kpt prefix source matching or other B3 tests,
nor a global diary-uniform BRD characterization.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Filter the physical FINAL original-stage auxiliary E-free
endpoints to the TRUE OLD scan range, excluding c=oldTop itself.

The underlying final pool includes all selected old parameter
originals, not merely the literal root U∪{w}. -/
noncomputable def KptPhysicalOldRangeStageFreeEnds
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (U : Finset (Fin M)) (w : Fin M)
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) : Finset Nat := by
  classical
  exact (KptPhysicalFinalStageFreeEnds
    family L k M (U ∪ {w}) X oldTop Rold).filter
      (fun cut => cut < oldTop)

/-- Membership is EXACTLY membership in the complete physical
free-end exception image plus strict position below oldTop. -/
theorem mem_KptPhysicalOldRangeStageFreeEnds_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (U : Finset (Fin M)) (w : Fin M)
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (cut : Nat) :
    cut ∈ KptPhysicalOldRangeStageFreeEnds
      family L k M U w X oldTop Rold ↔
    cut ∈ KptPhysicalFinalStageFreeEnds
      family L k M (U ∪ {w}) X oldTop Rold ∧
      cut < oldTop := by
  classical
  simp only [KptPhysicalOldRangeStageFreeEnds, Finset.mem_filter]

/-- The new original root w adds NO exceptional E-free endpoint
below the old scan top, provided oldTop≤freeLevel(w).

All actual physical selected old parameter originals stay in
the complete stage hStageOriginals and are counted using the
verified E86 cardinal injection into actual selected old levels.

There is no assumption that w is a fresh numerical address or
that freeLevel is injective; U may already contain w. -/
theorem kpt_physical_oldrange_freeends_card_le_roots_add_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (U : Finset (Fin M)) (w : Fin M)
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (hNewAbove :
      oldTop ≤ (finiteNumericH L k M).freeLevel w.val) :
    (KptPhysicalOldRangeStageFreeEnds
      family L k M U w X oldTop Rold).card ≤
      U.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH L k M
  let S : Finset (Fin M) :=
    hStageOriginals L k M U (Rold.I 0)
  let F : Finset Nat :=
    KptPhysicalOldRangeStageFreeEnds
      family L k M U w X oldTop Rold
  have hSub : F ⊆ S.image (fun v : Fin M => A.freeLevel v.val) := by
    intro cut hCutF
    have hFilter :=
      (mem_KptPhysicalOldRangeStageFreeEnds_iff
        family L k M U w X oldTop Rold cut).mp hCutF
    have hBelow : cut < oldTop := hFilter.2
    have hFull : cut ∈
        (hStageOriginals L k M (U ∪ {w}) (Rold.I 0)).image
          (fun v : Fin M => A.freeLevel v.val) := by
      simpa only [KptPhysicalFinalStageFreeEnds] using hFilter.1
    obtain ⟨v,hStage,hEq⟩ := Finset.mem_image.mp hFull
    have hOr :
        v ∈ U ∪ {w} ∨
          (v.val ∈ Rold.I 0 ∧ 0 < A.freeLevel v.val) := by
      simpa only [hStageOriginals, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        using hStage
    have hOldOr :
        v ∈ U ∨
          (v.val ∈ Rold.I 0 ∧ 0 < A.freeLevel v.val) := by
      rcases hOr with hRoot | hSelected
      · rcases Finset.mem_union.mp hRoot with hOld | hNew
        · exact Or.inl hOld
        · have hvw : v = w := Finset.mem_singleton.mp hNew
          subst v
          have hBoundA : oldTop ≤ A.freeLevel w.val := hNewAbove
          omega
      · exact Or.inr hSelected
    have hOldStage : v ∈ S := by
      simpa only [S, hStageOriginals, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        using hOldOr
    exact Finset.mem_image.mpr ⟨v,hOldStage,hEq⟩
  calc
    F.card ≤ (S.image (fun v : Fin M => A.freeLevel v.val)).card :=
      Finset.card_le_card hSub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ U.card +
        (kpt_old_actual_selected_levels family X oldTop Rold).card :=
      finiteNumericH_old_run_final_stage_originals_card_le_root_add_selected
        family L k M U X oldTop Rold

end Kk

#check @Kk.mem_KptPhysicalOldRangeStageFreeEnds_iff
#print axioms Kk.mem_KptPhysicalOldRangeStageFreeEnds_iff
#check @Kk.kpt_physical_oldrange_freeends_card_le_roots_add_selected
#print axioms Kk.kpt_physical_oldrange_freeends_card_le_roots_add_selected
