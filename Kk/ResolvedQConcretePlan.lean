import Kk.PositiveGenerationStructural
import Kk.TrackDOddTopSeedPlanSkip
import SuccessorTree.V10.HFinalPoolPositiveGeneration
import Mathlib.Tactic

/-!
# Concrete retained Plan, free-cut closure and descending inclusion
English-first audit: docs/generation_zero_concrete_plan_english_20261124.md.
This constructs the Plan from the proposed role assignment, not that role
assignment from a global Q schedule. No common labelled source is asserted.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10

def resolvedQRetainedReal (role : Nat → ResolvedQBaseRole)
    (k x : Nat) : Prop :=
  ∃ j m : Nat, m ≤ k ∧ x = hPosition k j m ∧
    ((role j = .coded true ∧ m = k) ∨
      ∃ block : Nat, role j = .auxiliary block true)

def resolvedQConcretePlan (K : AgeTestModel 1 0 1)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) : Set Nat :=
  {x | x = 0 ∨ x = (finiteNumericH K k N).freeLevel cap.val ∨
    resolvedQRetainedReal role k x ∨
    ∃ v : Fin N, resolvedQRetainedReal role k v.val ∧
      0 < (finiteNumericH K k N).freeLevel v.val ∧
      x = (finiteNumericH K k N).freeLevel v.val}

theorem resolvedQConcretePlan_top_mem (K : AgeTestModel 1 0 1)
    (k N : Nat) (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    (finiteNumericH K k N).freeLevel cap.val ∈
      resolvedQConcretePlan K k N cap role :=
  Or.inr (Or.inl rfl)

theorem resolvedQConcretePlan_positive_original_retained
    (K : AgeTestModel 1 0 1) (k N : Nat) (hk : 0 < k)
    (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N) (hv : v.val ∈ resolvedQConcretePlan K k N cap role)
    (hPos : 0 < (finiteNumericH K k N).freeLevel v.val) :
    resolvedQRetainedReal role k v.val := by
  obtain ⟨j,m,_hm,hmk,hAddr⟩ :=
    finiteNumericH_positive_freeCut_has_real_positive_generation K k N hk v hPos
  change v.val = 0 ∨ v.val = (finiteNumericH K k N).freeLevel cap.val ∨
    resolvedQRetainedReal role k v.val ∨
    ∃ w : Fin N, resolvedQRetainedReal role k w.val ∧
      0 < (finiteNumericH K k N).freeLevel w.val ∧
      v.val = (finiteNumericH K k N).freeLevel w.val at hv
  have hVPos : 0 < v.val := lt_of_lt_of_le hPos
    ((finiteNumericH K k N).freeLevel_le v.val)
  rcases hv with hZero | hCap | hReal | ⟨w,_hRet,hWPos,hW⟩
  · omega
  · have hCapPos : 0 < (finiteNumericH K k N).freeLevel cap.val := by omega
    exact False.elim ((finiteNumericH_positive_freeLevel_ne_realPosition
      K k N cap.val j m cap.isLt hCapPos) (hCap.symm.trans hAddr))
  · exact hReal
  · exact False.elim ((finiteNumericH_positive_freeLevel_ne_realPosition
      K k N w.val j m w.isLt hWPos) (hW.symm.trans hAddr))

theorem resolvedQConcretePlan_role_contract
    (K : AgeTestModel 1 0 1) (k N : Nat) (hk : 0 < k)
    (cap : Fin N) (role : Nat → ResolvedQBaseRole)
    (v : Fin N) (hv : v.val ∈ resolvedQConcretePlan K k N cap role)
    (hPos : 0 < (finiteNumericH K k N).freeLevel v.val)
    (j m : Nat) (hm : m ≤ k) (hAddr : v.val = hPosition k j m) :
    (role j = .coded true ∧ m = k) ∨
      ∃ block : Nat, role j = .auxiliary block true := by
  obtain ⟨j',m',hm',hAddr',hRole⟩ :=
    resolvedQConcretePlan_positive_original_retained K k N hk cap role v hv hPos
  obtain ⟨hJ,hM⟩ := hPosition_injective_bounded k j m j' m' hm hm'
    (hAddr.symm.trans hAddr')
  subst j'
  subst m'
  exact hRole

theorem resolvedQConcretePlan_free_closed
    (K : AgeTestModel 1 0 1) (k N : Nat) (hk : 0 < k)
    (cap : Fin N) (role : Nat → ResolvedQBaseRole) :
    ∀ v : Fin N, v.val ∈ resolvedQConcretePlan K k N cap role →
      0 < (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).freeLevel v.val ∈
        resolvedQConcretePlan K k N cap role := by
  intro v hv hPos
  have hRet := resolvedQConcretePlan_positive_original_retained K k N hk
    cap role v hv hPos
  exact Or.inr (Or.inr (Or.inr ⟨v,hRet,hPos,rfl⟩))

theorem resolvedQ_dummy_cap_bounded_role
    (role : Nat → ResolvedQBaseRole) (k N : Nat) (cap : Fin N)
    (base : Nat) (hCap : cap.val = hPosition k base k)
    (hDummy : role base = .dummy) :
    ∀ j m : Nat, m ≤ k → cap.val = hPosition k j m → role j = .dummy := by
  intro j m hm hAddr
  obtain ⟨hJ,_⟩ := hPosition_injective_bounded k base k j m le_rfl hm
    (hCap.symm.trans hAddr)
  simpa only [←hJ] using hDummy

/-- Pure descending assembly of LOCAL skip implications. This proves
inclusion for the minimal run, not a forced-retention run or coverage. -/
theorem actualRun_final_subset_plan_of_local_omissions
    (family : List (NormalizedForbidden 1 0 1))
    (X : Set (AdmissibleKptNode family)) (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top)
    (Plan : Set Nat) (hTop : top ∈ Plan)
    (hSkip : ∀ i : Nat, i < top → i ∉ Plan →
      Run.I (i+1) ⊆ Plan → i ∉ Run.I 0) :
    Run.I 0 ⊆ Plan := by
  have hAll : ∀ d i : Nat, top - i = d → i ≤ top → Run.I i ⊆ Plan := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hD hLe
      by_cases hEq : i = top
      · subst i
        rw [Run.topI]
        intro q hq
        have hq' : q = top := Set.mem_singleton_iff.mp hq
        simpa only [hq'] using hTop
      · have hi : i < top := by omega
        have hNext := ih (top-(i+1)) (by omega) (i+1) rfl (by omega)
        rcases Run.level_step i hi with hKeep | hInsert
        · rw [hKeep]
          exact hNext
        · have hHere : i ∈ Run.I i := by
            rw [hInsert]
            exact Set.mem_insert i _
          rw [Run.I_eq_final_tail_of_run i hLe] at hHere
          have hFinal : i ∈ Run.I 0 := hHere.1
          have hIn : i ∈ Plan := by
            by_contra hNot
            exact hSkip i hi hNot hNext hFinal
          rw [hInsert]
          intro q hq
          rcases Set.mem_insert_iff.mp hq with hq' | hq'
          · simpa only [hq'] using hIn
          · exact hNext hq'
  exact hAll top 0 (by simp) (Nat.zero_le top)

end Kk
