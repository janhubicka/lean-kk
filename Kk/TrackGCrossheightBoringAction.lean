import Kk.TrackGBoringAncestorOverlap
import Kk.TrackEOldPhysicalIndexRetention
import Mathlib.Tactic

/-!
# Track G: growing-height nested actual Kpt runs agree on old boring ancestors.

English proof and 18 hostile checks committed BEFORE Lean:
docs/track_g_crossheight_boring_factor_action_english_audit_20261118.md

Track E E60 gives ACTUAL complete old-to-new Kpt closure inclusion under
nested seeds, old-top seed and height growth. Track G #331 gives
literal overlap action equality for both genuinely boring runs.
Together they imply that the two total monoid factors agree on EVERY
eligible OLD high-end physical source ancestor. No reverse transport
of new-only auxiliary nodes or labelled cross-diary orbit is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- For nested actual seeds and genuine height growth, two runs
boring on the entire same old-range interval have identical
accumulated monoid action on every high-enough node of the OLD
full parameter-closed Kpt source. New-only nodes are not covered.

This uses the ACTUAL old top seed and the strict old-range cut
hypothesis from E60; not a source-index surjectivity assumption. -/
theorem crossheight_actual_boring_factor_agrees_on_old_Kpt_source
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
    (low cut : Nat) (hLowCut : low ≤ cut+1)
    (hCut : cut < oldTop)
    (hBoringOld : ∀ i : Nat, low ≤ i → i < cut+1 →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (i+1)) X) i)
    (hBoringNew : ∀ i : Nat, low ≤ i → i < cut+1 →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (i+1)) Y) i) :
    ∃ Dold Dnew : MMap (normalizedKptSMTree family),
      RunOld.F low =
        MMap.comp (normalizedKptSMTree family)
          (RunOld.F (cut+1)) Dold ∧
      RunNew.F low =
        MMap.comp (normalizedKptSMTree family)
          (RunNew.F (cut+1)) Dnew ∧
      ∀ (c : AdmissibleKptNode family)
        (hcOld : c ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunOld.I (cut+1)) X)
        (hLev : cut+1 ≤ LevelTree.lev c),
        Dold (LevelTree.ancestor c low (le_trans hLowCut hLev)) =
          Dnew (LevelTree.ancestor c low (le_trans hLowCut hLev)) := by
  obtain ⟨Dold, Dnew, hDold, hDnew, hOverlap⟩ :=
    actualAlgorithmRuns_boring_factors_agree_on_physical_overlap
      (normalizedKptSMTree family) X Y oldTop newTop
      low (cut+1) RunOld RunNew hLowCut
      (by omega) (by omega) hBoringOld hBoringNew
  refine ⟨Dold, Dnew, hDold, hDnew, ?_⟩
  intro c hcOld hLev
  have hcNew :
      c ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunNew.I (cut+1)) Y :=
    crossheight_actual_preCut_Kpt_source_subset
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew cut hCut hcOld
  exact hOverlap c hcOld hcNew hLev

end Kk
