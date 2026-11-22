import Kk.TrackESelectedLevelOriginalBudget
import Mathlib.Tactic

/-!
# Track E E87: selected OLD suffix bounds needed physical original max tests

English-first proof, 22 hostile adversarial checks:
docs/track_e_selected_tail_source_budget_english_audit_20261122.md

E86 bounds the number of distinct physical numerical-H+ originals
requiring maximal complete OLD Kpt-prefix checks by U.card plus
the number of ALL actual OLD selected source levels R.I(0).

If every Allowed tested cut is >= a cutoff floor < oldTop, each
genuinely eligible original already lies in the actual physical
stage pool at R.I(floor+1). Thus the number of different tests
is bounded more sharply by U.card plus only the number of
ACTUALLY selected OLD levels that SURVIVE in R.I(floor+1).

The source is a genuine OLD AlgorithmRun and all candidate NEW
closure membership uses its unchanged selected tail. No target
AlgorithmRun, selected graph-age shadow, common diary source-orbit
or diary-uniform bound is asserted or assumed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The finite exact set of selected OLD source levels surviving
at the actual scan tail R.I(floor+1). The inclusive oldTop
belongs to the range, because topI={oldTop}. The definition
is useful only for floor < oldTop in our source-count results. -/
noncomputable def kpt_old_actual_selected_tail_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (floor : Nat) : Finset Nat := by
  classical
  exact (Finset.range (top+1)).filter
    (fun q => q ∈ R.I (floor+1))

/-- The selected tail Finset is EXACTLY the actual OLD selected
source level set R.I(floor+1), for floor < oldTop. All selected
level bounds and top inclusivity come from genuine AlgorithmRun. -/
theorem mem_kpt_old_actual_selected_tail_levels_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (floor : Nat) (hFloor : floor < top)
    (q : Nat) :
    q ∈ kpt_old_actual_selected_tail_levels family X top R floor ↔
      q ∈ R.I (floor+1) := by
  classical
  simp only [kpt_old_actual_selected_tail_levels,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro hSelected
    have hBound : q ≤ top :=
      (R.I_mem_bounds (floor+1) (by omega) q hSelected).2
    exact ⟨Nat.lt_succ_of_le hBound,hSelected⟩

/-- E87 stage-suffix containment: if ALL Allowed source cuts
are >= floor<oldTop, every physical original that actually has
a NONEMPTY E79 old-boring/new-live crossing support belongs
to the ONE true physical original stage at old R.I(floor+1).

This improves E85's inclusion in the FINAL stage at old R.I0,
without claiming the original is itself an old-live Kpt source. -/
theorem kpt_originals_needing_max_socle_subset_old_selected_tail_stage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (floor : Nat) (hFloor : floor < top)
    (hAllowedFloor : ∀ c : Nat, c ∈ Allowed → floor ≤ c) :
    kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed ⊆
    hStageOriginals K k N U (R.I (floor+1)) := by
  classical
  intro v hv
  have hNonempty :=
    (mem_kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed v).mp hv
  obtain ⟨cut,hCut⟩ := hNonempty
  have hAllowed : cut ∈ Allowed :=
    ((mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mp hCut).2
  have hBase :
      cut ∈ kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v :=
    ((mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mp hCut).1
  have hData :=
    (mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v cut).mp hBase
  have hCutTop : cut < top := hData.1
  have hStage :
      v ∈ hStageOriginals K k N U (R.I (cut+1)) :=
    hData.2.2.1
  have hLe : floor ≤ cut := hAllowedFloor cut hAllowed
  have hLevels : R.I (cut+1) ⊆ R.I (floor+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    rw [R.I_eq_final_tail_of_run (floor+1) (by omega)]
    exact ⟨hq.1,by omega⟩
  exact finiteNumericH_stageOriginals_mono_levels
    K k N U (R.I (cut+1)) (R.I (floor+1)) hLevels hStage

/-- The TRUE old selected original-stage pool at floor+1 has
at most |U| plus the number of actually selected OLD levels
SURVIVING in R.I(floor+1). The bound is independent of N and
ignores both early selected blocks and all boring numerical gaps.

There is no assumption that U and the selected original
addresses are disjoint. -/
theorem finiteNumericH_old_selected_tail_stage_card_le_root_add_selected_tail
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (floor : Nat) (hFloor : floor < top) :
    (hStageOriginals K k N U (R.I (floor+1))).card ≤
      U.card + (kpt_old_actual_selected_tail_levels
        family X top R floor).card := by
  classical
  let V : Finset (Fin N) :=
    hStageOriginals K k N U (R.I (floor+1))
  let T : Finset (Fin N) :=
    Finset.univ.filter (fun v : Fin N => v.val ∈ R.I (floor+1))
  let Sel : Finset Nat :=
    kpt_old_actual_selected_tail_levels family X top R floor
  have hSub : V ⊆ U ∪ T := by
    intro v hv
    have hvOr :
        v ∈ U ∨
          (v.val ∈ R.I (floor+1) ∧
            0 < (finiteNumericH K k N).freeLevel v.val) := by
      simpa only [V, hStageOriginals, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    rcases hvOr with hRoot | ⟨hSelected,_hFree⟩
    · exact Finset.mem_union.mpr (Or.inl hRoot)
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ v,hSelected⟩
  have hTBound : T.card ≤ Sel.card := by
    apply Finset.card_le_card_of_injOn
      (s := T) (t := Sel) (fun v : Fin N => v.val)
    · intro v hv
      have hSelected : v.val ∈ R.I (floor+1) :=
        (Finset.mem_filter.mp hv).2
      change v.val ∈
        kpt_old_actual_selected_tail_levels family X top R floor
      exact (mem_kpt_old_actual_selected_tail_levels_iff
        family X top R floor hFloor v.val).mpr hSelected
    · intro v _hv w _hw heq
      exact Fin.ext heq
  have hVCard : V.card ≤ (U ∪ T).card :=
    Finset.card_le_card hSub
  have hUnionCard : (U ∪ T).card ≤ U.card + T.card :=
    Finset.card_union_le U T
  change V.card ≤ U.card + Sel.card
  omega

/-- E87 quantitative suffix bound: count only physical originals
requiring one maximal COMPLETE OLD Kpt-prefix test at Allowed
old-boring cuts AT OR ABOVE floor.

The number of such original tests is bounded by the genuine
old root original pool plus the number of actually selected
OLD levels STILL in the stage tail R.I(floor+1).

This controls test carriers, NOT witness existence, number
of bad cuts, diary-uniformity, or common labelled inverse orbit. -/
theorem kpt_originals_needing_max_old_socle_test_card_le_root_add_selected_tail
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (floor : Nat) (hFloor : floor < top)
    (hAllowedFloor : ∀ c : Nat, c ∈ Allowed → floor ≤ c) :
    (kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed).card ≤
      U.card + (kpt_old_actual_selected_tail_levels
        family X top R floor).card := by
  have hSub :=
    kpt_originals_needing_max_socle_subset_old_selected_tail_stage
      family K k N hAvoid U X Y top R Allowed
      floor hFloor hAllowedFloor
  have hCard := Finset.card_le_card hSub
  have hStageBound :=
    finiteNumericH_old_selected_tail_stage_card_le_root_add_selected_tail
      family K k N U X top R floor hFloor
  exact hCard.trans hStageBound

/-- Selected levels surviving after floor are ACTUALLY selected
OLD levels in R.I0. Thus the suffix budget never exceeds E86's
all-old-selected-level budget. Genuine topI is included. -/
theorem kpt_old_actual_selected_tail_subset_all_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (floor : Nat) (hFloor : floor < top) :
    kpt_old_actual_selected_tail_levels family X top R floor ⊆
      kpt_old_actual_selected_levels family X top R := by
  intro q hq
  have hTail : q ∈ R.I (floor+1) :=
    (mem_kpt_old_actual_selected_tail_levels_iff
      family X top R floor hFloor q).mp hq
  have hFinal : q ∈ R.I 0 := by
    rw [R.I_eq_final_tail_of_run (floor+1) (by omega)] at hTail
    exact hTail.1
  exact (mem_kpt_old_actual_selected_levels_iff
    family X top R q).mpr hFinal

end Kk
