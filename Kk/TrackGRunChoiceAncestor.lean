import Kk.TrackGBoringAncestorOverlap
import Kk.TrackGArbitraryBlockFactor
import Mathlib.Tactic

/-!
# Track G: genuine boring action is independent of AlgorithmRun choices.

English proof and 10 hostile checks FIRST:
docs/track_g_run_choice_ancestor_english_audit_20261118.md

For the SAME seed set X, the successor-tree verified I_eq theorem
forces all actual runs to use the same selected level sets.
G318 translates I endpoint equality to all-boringness on their own
complete pre-cut sources. G331 then makes both accumulated factors
act identically on all high-end full source-node ancestors.

Not a theorem about different seed sets, disjoint diary occurrences
or uniform bounded labelled orbit/carrier; no E1 is used.
-/

namespace Kk

universe u v

open SuccessorTree
open SuccessorTree.SMTree

/-- At a fixed actual seed set and top, the restricted boring-block
monoid action on the complete surviving high source is independent
of every choice of run. The unique total factors themselves need
not be equal outside that high-source ancestor carrier. -/
theorem actualAlgorithmRuns_same_seeds_boring_action_choice_independent
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S) (X : Set T)
    (top low high : Nat)
    (R R' : SMTree.Envelope.AlgorithmRun H X top)
    (hLowHigh : low ≤ high) (hHigh : high ≤ top)
    (hSelected : R.I low = R.I high) :
    ∃ D E : MMap H,
      R.F low = MMap.comp H (R.F high) D ∧
      R'.F low = MMap.comp H (R'.F high) E ∧
      ∀ (c : T)
        (hc : c ∈ SMTree.Envelope.closure S (R.I high) X)
        (hlev : high ≤ LevelTree.lev c),
        D (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
          E (LevelTree.ancestor c low (le_trans hLowHigh hlev)) ∧
        D (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
          LevelTree.ancestor c high hlev := by
  have hIlo : R.I low = R'.I low :=
    R.I_eq R' low (by omega)
  have hIhi : R.I high = R'.I high :=
    R.I_eq R' high hHigh
  have hSelected' : R'.I low = R'.I high := by
    calc
      R'.I low = R.I low := hIlo.symm
      _ = R.I high := hSelected
      _ = R'.I high := hIhi
  have hBoring :
      ∀ i : Nat, low ≤ i → i < high →
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (i+1)) X) i :=
    (actualAlgorithmRun_I_equal_iff_all_genuinely_boring
      H X top low high R hLowHigh hHigh).mp hSelected
  have hBoring' :
      ∀ i : Nat, low ≤ i → i < high →
        ¬ SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R'.I (i+1)) X) i :=
    (actualAlgorithmRun_I_equal_iff_all_genuinely_boring
      H X top low high R' hLowHigh hHigh).mp hSelected'
  obtain ⟨D, ⟨hDF, hDA⟩, _⟩ :=
    actualAlgorithmRun_boring_block_unique_factor_ancestor_action
      H X top low high R hLowHigh hHigh hBoring
  obtain ⟨E, ⟨hEF, hEA⟩, _⟩ :=
    actualAlgorithmRun_boring_block_unique_factor_ancestor_action
      H X top low high R' hLowHigh hHigh hBoring'
  refine ⟨D, E, hDF, hEF, ?_⟩
  intro c hc hlev
  have hc' :
      c ∈ SMTree.Envelope.closure S (R'.I high) X := by
    rw [← hIhi]
    exact hc
  constructor
  · calc
      D (LevelTree.ancestor c low (le_trans hLowHigh hlev)) =
        LevelTree.ancestor c high hlev := hDA c hc hlev
      _ = E (LevelTree.ancestor c low (le_trans hLowHigh hlev)) :=
        (hEA c hc' hlev).symm
  · exact hDA c hc hlev

end Kk
