import Kk.TrackGArbitraryBlockFactor
import Mathlib.Tactic

/-!
# Track G: a genuinely boring block acts canonically on actual Kpt ancestors.

English proof and 16 hostile checks were committed FIRST:
docs/track_g_boring_ancestor_overlap_english_audit_20261118.md

The one-run accumulated total monoid factor D maps each actual lower-cut
ancestor of every full-closure node surviving through the high endpoint
to the corresponding high-cut ancestor. This gives a genuine restricted
two-run agreement on literal overlapping physical Kpt nodes, even for
different seed sets and independent skip-map choices.

It does NOT identify disjoint diary occurrences, transport different
cut-coordinate systems, equate the total factors, or bound labels/BRDs.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree

/-- For a complete genuinely boring interval of ONE actual run,
the unique accumulated total factor acts by the precise physical
ancestor jump low -> high on EVERY live node of the high-end
FULL parameter-closed source. No selected-front projection. -/
theorem actualAlgorithmRun_boring_block_unique_factor_ancestor_action
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top)
    (hBoring : ∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (R.I (i+1)) X) i) :
    ∃! D : MMap H,
      R.F low = MMap.comp H (R.F high) D ∧
      ∀ (c : T)
        (hc : c ∈ SMTree.Envelope.closure S (R.I high) X)
        (hlev : high ≤ LevelTree.lev c),
        D (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
          LevelTree.ancestor c high hlev := by
  have main :
      ∀ d : Nat, ∀ i : Nat,
        (hdi : high - i = d) →
        (hlo : low ≤ i) → (hi : i ≤ high) →
        ∃ D : MMap H,
          R.F i = MMap.comp H (R.F high) D ∧
          ∀ (c : T)
            (hc : c ∈ SMTree.Envelope.closure S (R.I high) X)
            (hlev : high ≤ LevelTree.lev c),
            D (LevelTree.ancestor c i (le_trans hi hlev)) =
              LevelTree.ancestor c high hlev := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hlo hi
        by_cases hieq : i = high
        · subst i
          refine ⟨MMap.id H, ?_, ?_⟩
          · apply MMap.ext_apply
            intro z
            rfl
          · intro c hc hlev
            rfl
        · have hilt : i < high :=
            lt_of_le_of_ne hi hieq
          have hitop : i < top :=
            lt_of_lt_of_le hilt hHigh
          have hNextHigh : i + 1 ≤ high := by omega
          obtain ⟨E, hEF, hEA⟩ :=
            ih (high - (i+1)) (by omega) (i+1) rfl
              (by omega) hNextHigh
          have hBoringNext :
              ∀ j : Nat, i+1 ≤ j → j < high →
                ¬ SMTree.Envelope.IsInterestingAt H
                  (SMTree.Envelope.closure S (R.I (j+1)) X) j := by
            intro j hjLow hjHigh
            exact hBoring j (by omega) hjHigh
          have hNextI : R.I (i+1) = R.I high :=
            (actualAlgorithmRun_genuinely_boring_block_factors
              H X top (i+1) high R hNextHigh hHigh hBoringNext).1
          obtain ⟨Di, _hSkip, hCross, _hI, hFi⟩ :=
            R.noninteresting_step i hitop (hBoring i hlo hilt)
          refine ⟨MMap.comp H E Di, ?_, ?_⟩
          · calc
              R.F i = MMap.comp H (R.F (i+1)) Di := hFi
              _ = MMap.comp H
                    (MMap.comp H (R.F high) E) Di := by rw [hEF]
              _ = MMap.comp H
                    (R.F high) (MMap.comp H E Di) := by
                      apply MMap.ext_apply
                      intro z
                      rfl
          · intro c hc hlev
            have hcNext :
                c ∈ SMTree.Envelope.closure S (R.I (i+1)) X := by
              rw [hNextI]
              exact hc
            have hAt :
                Di (LevelTree.ancestor c i (le_trans hi hlev)) =
                  LevelTree.ancestor c (i+1) (le_trans hNextHigh hlev) := by
              simpa using
                (hCross hcNext (show i < LevelTree.lev c by omega))
            calc
              (MMap.comp H E Di)
                  (LevelTree.ancestor c i (le_trans hi hlev)) =
                E (Di (LevelTree.ancestor c i (le_trans hi hlev))) := rfl
              _ = E (LevelTree.ancestor c (i+1)
                        (le_trans hNextHigh hlev)) := by rw [hAt]
              _ = LevelTree.ancestor c high hlev := hEA c hc hlev
  obtain ⟨D, hDF, hDA⟩ :=
    main (high-low) low rfl le_rfl hLowHigh
  refine ⟨D, ⟨hDF, hDA⟩, ?_⟩
  intro E hE
  exact (kpt_MMap_comp_left_cancel H (R.F high) D E
    (hDF.symm.trans hE.1)).symm

/-- Two actual runs on possibly DIFFERENT seed sets in the SAME
physical tree have identical action of their genuine boring-block
factors on ancestors of literal full-source nodes common to both.

This is strictly weaker than a common labelled orbit between disjoint
diary occurrences: no physical node identification or cut reindexing
is constructed, and the total MMaps may differ outside the overlap. -/
theorem actualAlgorithmRuns_boring_factors_agree_on_physical_overlap
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X Y : Set T)
    (topX topY low high : Nat)
    (RX : SMTree.Envelope.AlgorithmRun H X topX)
    (RY : SMTree.Envelope.AlgorithmRun H Y topY)
    (hLowHigh : low ≤ high)
    (hHighX : high ≤ topX) (hHighY : high ≤ topY)
    (hBoringX : ∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RX.I (i+1)) X) i)
    (hBoringY : ∀ i : Nat, low ≤ i → i < high →
      ¬ SMTree.Envelope.IsInterestingAt H
        (SMTree.Envelope.closure S (RY.I (i+1)) Y) i) :
    ∃ DX DY : MMap H,
      RX.F low = MMap.comp H (RX.F high) DX ∧
      RY.F low = MMap.comp H (RY.F high) DY ∧
      ∀ (c : T)
        (hcX : c ∈ SMTree.Envelope.closure S (RX.I high) X)
        (hcY : c ∈ SMTree.Envelope.closure S (RY.I high) Y)
        (hlev : high ≤ LevelTree.lev c),
        DX (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
          DY (LevelTree.ancestor c low (le_trans hLowHigh hlev)) := by
  obtain ⟨DX, ⟨hDX, hAX⟩, _⟩ :=
    actualAlgorithmRun_boring_block_unique_factor_ancestor_action
      H X topX low high RX hLowHigh hHighX hBoringX
  obtain ⟨DY, ⟨hDY, hAY⟩, _⟩ :=
    actualAlgorithmRun_boring_block_unique_factor_ancestor_action
      H Y topY low high RY hLowHigh hHighY hBoringY
  refine ⟨DX, DY, hDX, hDY, ?_⟩
  intro c hcX hcY hlev
  calc
    DX (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
      LevelTree.ancestor c high hlev := hAX c hcX hlev
    _ = DY (LevelTree.ancestor c low (le_trans hLowHigh hlev)) :=
      (hAY c hcY hlev).symm

end Kk
