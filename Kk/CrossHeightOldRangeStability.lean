import Kk.CrossHeightNewRootNovelty
import Kk.NoNewRootEventCriterion
import Mathlib.Tactic

/-!
# Track E: old-range selected-level stability across DIFFERENT scan tops

If an enlarged genuine Kpt AlgorithmRun has a new top, its complete
selected-level set CANNOT equal the old run's selected-level set:
at a minimum the new top itself is present.

The correct comparison is the OLD HEIGHT RESTRICTION of the new run.
A one-sided, physically meaningful NO-NOVELTY hypothesis at every
cut STRICTLY below oldTop prevents any additional old-range levels.

The proof combines the kernel-checked crossheight seed monotonicity
and the genuinely physical new-cut terminal-or-L+ crossing witness
theorem. There is no profile-equivalence/orbit axiom.

English-first adversarial audit:
  docs/track_e_crossheight_new_root_novelty_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Actual growing-height AlgorithmRuns have the SAME FINAL
selected-level skeleton **restricted to the OLD scan height**
provided there is no new terminal source or complete old/upper
dependent-L+ crossing pair below oldTop.

Importantly the proof DOES NOT assert RunOld.I0=RunNew.I0:
the new run can have selected levels strictly ABOVE oldTop.

The one-sided physical hNoNovelty condition compares the complete
REAL pre-cut parameter-closed source of each run at its own ACTUAL
chosen higher level set. The reverse source inclusion follows from
seed growth, genuine I1/I2/I3 monotonicity and a real top seed.

New Kpt parameters, negative atoms, auxiliary E and actual I2
forks are retained in the no-new FULL crossing-pair test. -/
theorem crossheight_runs_final_old_range_eq_of_no_novelty
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
    (hNoNovelty : ∀ cut : Nat, cut < oldTop →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y) cut) :
    RunOld.I 0 = {q : Nat | q ∈ RunNew.I 0 ∧ q ≤ oldTop} := by
  have hMonotone :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      (normalizedKptSMTree family)
      X Y hXY oldTop newTop hTopLe hTopSeed RunOld RunNew
  have hOldTopFinal : oldTop ∈ RunOld.I 0 := by
    have hTop : oldTop ∈ RunOld.I oldTop := by
      rw [RunOld.topI]
      exact Set.mem_singleton_iff.mpr rfl
    rw [RunOld.I_eq_final_tail_of_run oldTop (le_refl _)] at hTop
    exact hTop.1
  ext q
  constructor
  · intro hOld
    have hNew : q ∈ RunNew.I 0 :=
      (hMonotone 0 (Nat.zero_le oldTop)) hOld
    have hBound : q ≤ oldTop :=
      (RunOld.I_mem_bounds 0 (Nat.zero_le oldTop) q hOld).2
    exact ⟨hNew,hBound⟩
  · rintro ⟨hNew,hBound⟩
    by_cases hTop : q = oldTop
    · subst q
      exact hOldTopFinal
    · have hCut : q < oldTop := lt_of_le_of_ne hBound hTop
      by_contra hNotOld
      have hNewAt : q ∈ RunNew.I q := by
        rw [RunNew.I_eq_final_tail_of_run q (by omega)]
        exact ⟨hNew,le_refl q⟩
      have hNotOldAt : q ∉ RunOld.I q := by
        intro hStage
        rw [RunOld.I_eq_final_tail_of_run q (by omega)] at hStage
        exact hNotOld hStage.1
      have hNovel :=
        crossheight_new_selected_Kpt_cut_has_new_terminal_or_full_crossing
          family X Y hXY oldTop newTop q hTopLe hTopSeed
          RunOld RunNew hCut hNewAt hNotOldAt
      let ZX : Set (AdmissibleKptNode family) :=
        SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (q+1)) X
      let ZY : Set (AdmissibleKptNode family) :=
        SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (q+1)) Y
      have hQuiet : NewRootNoNoveltyAtCut family ZX ZY q :=
        hNoNovelty q hCut
      rcases hNovel with ⟨z,hZY,hAbsent,hLev⟩ | ⟨p,hNewPair,hNotPair⟩
      · have hOldI1 : KptI1AtCut family ZX q :=
          hQuiet.1 ⟨z,hZY,hLev⟩
        have hOldInteresting :
            SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family) ZX q :=
          Or.inl hOldI1
        have hStep := (RunOld.interesting_step q hCut hOldInteresting).1
        have hStage : q ∈ RunOld.I q := by
          rw [hStep]
          exact Set.mem_insert_iff.mpr (Or.inl rfl)
        exact hNotOldAt hStage
      · exact hNotPair (hQuiet.2 hNewPair)

/-- At EVERY actual scan stage i≤oldTop, the old run's
selected-level set equals the NEW run's selected-level set
restricted to levels ≤oldTop. The new run may have many genuine
interesting levels above oldTop; these are not compared away.

The proof uses only the verified AlgorithmRun final-tail identity
and the preceding physically certified old-range final equality. -/
theorem crossheight_runs_all_old_range_levels_eq_of_no_novelty
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
    (hNoNovelty : ∀ cut : Nat, cut < oldTop →
      NewRootNoNoveltyAtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y) cut) :
    ∀ i : Nat, i ≤ oldTop →
      RunOld.I i = {q : Nat | q ∈ RunNew.I i ∧ q ≤ oldTop} := by
  have hFinal :=
    crossheight_runs_final_old_range_eq_of_no_novelty
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew hNoNovelty
  intro i hi
  ext q
  constructor
  · intro hOldStage
    have hOldFinal : q ∈ RunOld.I 0 ∧ i ≤ q := by
      rw [RunOld.I_eq_final_tail_of_run i hi] at hOldStage
      exact hOldStage
    have hNewFinal : q ∈ RunNew.I 0 ∧ q ≤ oldTop := by
      rw [hFinal] at hOldFinal
      exact ⟨hOldFinal.1.1,hOldFinal.1.2⟩
    have hNewStage : q ∈ RunNew.I i := by
      rw [RunNew.I_eq_final_tail_of_run i (by omega)]
      exact ⟨hNewFinal.1,hOldFinal.2⟩
    exact ⟨hNewStage,hNewFinal.2⟩
  · rintro ⟨hNewStage,hRange⟩
    have hNewFinal : q ∈ RunNew.I 0 ∧ i ≤ q := by
      rw [RunNew.I_eq_final_tail_of_run i (by omega)] at hNewStage
      exact hNewStage
    have hOldFinal : q ∈ RunOld.I 0 := by
      rw [hFinal]
      exact ⟨hNewFinal.1,hRange⟩
    rw [RunOld.I_eq_final_tail_of_run i hi]
    exact ⟨hOldFinal,hNewFinal.2⟩

end Kk
