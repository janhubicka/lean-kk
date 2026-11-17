import Kk.TrackGUniqueBoringBlockFactor
import Mathlib.Tactic

/-!
# Track G: every actual finite AlgorithmRun block factors through ONE
# uniquely determined total Kpt monoid map, even with interesting cuts.

English proof and fifteen hostile checks FIRST:
docs/track_g_arbitrary_block_factor_english_audit_20261117.md

This exposes an important limitation: the factorization alone is NOT a
boring-level compression, because it holds for ALL finite intervals.
The exact genuine boring criterion is equality of selected I sets.
No bounded labelled source, cross-occurrence transport or BRD is claimed.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree

/-- Any finite actual run interval, even one containing interesting
cuts, has exactly one accumulated TOTAL monoid factor. At interesting
cuts the stage map is the identity; at boring cuts it is the actual
noninteresting-step skip map. Uniqueness uses total map injectivity. -/
theorem actualAlgorithmRun_any_finite_block_unique_factor
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top) :
    ∃! D : MMap H, R.F low = MMap.comp H (R.F high) D := by
  have main :
      ∀ d : Nat, ∀ i : Nat, high - i = d → low ≤ i → i ≤ high →
        ∃ D : MMap H,
          R.F i = MMap.comp H (R.F high) D := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hlow hi
        by_cases hieq : i = high
        · subst i
          refine ⟨MMap.id H, ?_⟩
          apply MMap.ext_apply
          intro z
          rfl
        · have hilt : i < high :=
            lt_of_le_of_ne hi hieq
          have hitop : i < top :=
            lt_of_lt_of_le hilt hHigh
          obtain ⟨E, hE⟩ :=
            ih (high - (i+1)) (by omega) (i+1) rfl (by omega) (by omega)
          by_cases hinter :
              SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (R.I (i+1)) X) i
          · have hFi := (R.interesting_step i hitop hinter).2
            exact ⟨E, hFi.trans hE⟩
          · obtain ⟨Di, _hSkip, _hCross, _hI, hFi⟩ :=
              R.noninteresting_step i hitop hinter
            refine ⟨MMap.comp H E Di, ?_⟩
            calc
              R.F i = MMap.comp H (R.F (i+1)) Di := hFi
              _ = MMap.comp H
                    (MMap.comp H (R.F high) E) Di := by rw [hE]
              _ = MMap.comp H
                    (R.F high) (MMap.comp H E Di) := by
                      apply MMap.ext_apply
                      intro z
                      rfl
  obtain ⟨D, hD⟩ := main (high-low) low rfl le_rfl hLowHigh
  refine ⟨D, hD, ?_⟩
  intro E hE
  exact (kpt_MMap_comp_left_cancel H (R.F high) D E
    (hD.symm.trans hE)).symm

/-- An actual finite block keeps the selected I-set exactly when
EVERY cut in that block is genuinely boring on the COMPLETE Kpt
parameter-closed pre-cut source. Equal ordinary-L front ages are
not a substitute for this exact test (see the K4 cut-10/22 fixture). -/
theorem actualAlgorithmRun_I_equal_iff_all_genuinely_boring
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top) :
    R.I low = R.I high ↔
      ∀ i : Nat, low ≤ i → i < high →
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (i+1)) X) i := by
  constructor
  · intro hEq i hlow hihigh hinter
    have hitop : i < top := lt_of_lt_of_le hihigh hHigh
    have hiStage : i ∈ R.I i := by
      rw [(R.interesting_step i hitop hinter).1]
      simp
    have hiFinal : i ∈ R.I 0 := by
      rw [R.I_eq_final_tail_of_run i (by omega)] at hiStage
      exact hiStage.1
    have hiLow : i ∈ R.I low := by
      rw [R.I_eq_final_tail_of_run low (by omega)]
      exact ⟨hiFinal, hlow⟩
    rw [hEq] at hiLow
    have hTooHigh : high ≤ i :=
      (R.I_mem_bounds high hHigh i hiLow).1
    omega
  · intro hBoring
    exact (actualAlgorithmRun_genuinely_boring_block_factors
      H X top low high R hLowHigh hHigh hBoring).1

end Kk
