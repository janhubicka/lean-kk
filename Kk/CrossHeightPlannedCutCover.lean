import Kk.CrossHeightOldRangeStability
import Mathlib.Tactic

/-!
# Track E: planned extra-cut masks under genuine higher-top Kpt runs

The physical new-cut theorem implies a sharper relative criterion:
to rule out UNPLANNED interesting levels in the old scan range,
check the full physical no-novelty test only at cuts which were
boring in the old run and are not permitted by the resolved diary.

The allowed set is in COMMON SOURCE coordinates and must retain
auxiliary E and genuine K4 microcuts. No assumption that the
macrodiary exhausts physical event levels is made.

English-first proof and adversarial audit:
  docs/track_e_allowed_extra_cut_mask_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- If a cut strictly below the genuine old top is newly selected
in the taller run, then it must belong to Allowed, provided every
old-boring off-plan cut passes the ACTUAL full physical no-novelty
test (terminals and complete old/upper dependent L+ crossing pairs).

The hypothesis is required ONLY at old-boring OFF-PLAN cuts.
I2 forks and auxiliary E crossing pairs are kept in the physical
source relation; ordinary graph-age tests do not suffice. -/
theorem crossheight_extra_selected_cut_is_allowed_of_offplan_no_novelty
    {db du dd : Nat}
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
    (hNoOffPlan : ∀ cut : Nat, cut < oldTop →
      cut ∉ RunOld.I cut → cut ∉ Allowed →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y) cut) :
    ∀ cut : Nat, cut < oldTop →
      cut ∈ RunNew.I cut → cut ∉ RunOld.I cut →
      cut ∈ Allowed := by
  classical
  intro cut hCut hNew hOld
  by_contra hNotAllowed
  have hQuiet := hNoOffPlan cut hCut hOld hNotAllowed
  have hNovel :=
    crossheight_new_selected_Kpt_cut_has_new_terminal_or_full_crossing
      family X Y hXY oldTop newTop cut hTopLe hTopSeed
      RunOld RunNew hCut hNew hOld
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunOld.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunNew.I (cut+1)) Y
  change (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) at hNovel
  rcases hNovel with ⟨z,hZY,_hAbsent,hLev⟩ |
    ⟨p,hPair,hNotPair⟩
  · have hOldI1 : KptI1AtCut family ZX cut :=
      hQuiet.1 ⟨z,hZY,hLev⟩
    have hOldInteresting :
        SMTree.Envelope.IsInterestingAt
          (normalizedKptSMTree family) ZX cut :=
      Or.inl hOldI1
    have hStep :=
      (RunOld.interesting_step cut hCut hOldInteresting).1
    have hOldAt : cut ∈ RunOld.I cut := by
      rw [hStep]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hOld hOldAt
  · exact hNotPair (hQuiet.2 hPair)

/-- All new selected levels in the old scan range are either old
selected levels or members of the explicitly allowed set.

This is a SANDWICH, not equality: Allowed events need not actually
occur. New levels ABOVE oldTop remain unrestricted. -/
theorem crossheight_old_range_sandwich_of_offplan_no_novelty
    {db du dd : Nat}
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
    (hNoOffPlan : ∀ cut : Nat, cut < oldTop →
      cut ∉ RunOld.I cut → cut ∉ Allowed →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ oldTop →
      (RunOld.I i ⊆ RunNew.I i) ∧
      ({q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} ⊆
        RunOld.I i ∪ {q : Nat | q ∈ Allowed ∧ i ≤ q}) := by
  classical
  have hMonotone :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      (normalizedKptSMTree family)
      X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew
  have hPoint :=
    crossheight_extra_selected_cut_is_allowed_of_offplan_no_novelty
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew Allowed hNoOffPlan
  intro i hi
  constructor
  · exact hMonotone i hi
  · intro q hQ
    obtain ⟨hNewAtI,hRange⟩ := hQ
    have hNewTail : q ∈ RunNew.I 0 ∧ i ≤ q := by
      rw [RunNew.I_eq_final_tail_of_run i (by omega)] at hNewAtI
      exact hNewAtI
    by_cases hOldAtI : q ∈ RunOld.I i
    · exact Or.inl hOldAtI
    by_cases hAllowed : q ∈ Allowed
    · exact Or.inr ⟨hAllowed,hNewTail.2⟩
    have hCut : q < oldTop := by
      by_contra hNotCut
      have hEq : q = oldTop := by omega
      subst q
      have hOldTopStage : oldTop ∈ RunOld.I oldTop := by
        rw [RunOld.topI]
        exact Set.mem_singleton_iff.mpr rfl
      have hOldTopFinal : oldTop ∈ RunOld.I 0 := by
        rw [RunOld.I_eq_final_tail_of_run oldTop (le_refl _)]
          at hOldTopStage
        exact hOldTopStage.1
      have hOldHere : oldTop ∈ RunOld.I i := by
        rw [RunOld.I_eq_final_tail_of_run i hi]
        exact ⟨hOldTopFinal,hNewTail.2⟩
      exact hOldAtI hOldHere
    have hNewAtQ : q ∈ RunNew.I q := by
      rw [RunNew.I_eq_final_tail_of_run q (by omega)]
      exact ⟨hNewTail.1,le_refl q⟩
    have hOldNotAtQ : q ∉ RunOld.I q := by
      intro hOldStage
      have hOldFinal : q ∈ RunOld.I 0 := by
        rw [RunOld.I_eq_final_tail_of_run q (by omega)] at hOldStage
        exact hOldStage.1
      have hOldHere : q ∈ RunOld.I i := by
        rw [RunOld.I_eq_final_tail_of_run i hi]
        exact ⟨hOldFinal,hNewTail.2⟩
      exact hOldAtI hOldHere
    exact (hAllowed (hPoint q hCut hNewAtQ hOldNotAtQ)).elim

end Kk
