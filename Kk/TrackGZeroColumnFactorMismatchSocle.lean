import Kk.TrackEZeroColumnSocleCrossing
import Kk.TrackGExactFactorBadWitness
import Mathlib.Tactic

/-!
# Track G: a factor-disagreeing Kpt crossing at a TRUE zero ordinary-L
# stage cannot have ANY complete OLD Kpt lower-ancestor socle witness.

English proof and 12 hostile checks FIRST:
docs/track_g_zero_column_factor_mismatch_no_old_socle_english_audit_20261121.md

At a finite numerical-H+ graph stage with genuine ordinary-L
symmetry and ZERO cut columns for every eligible original,
E72 upgrades literal equality of complete OLD Kpt ancestors
to equality of complete UPPER ancestors as well.
G432 says an old-boring factor mismatch cannot have an old
witness for that COMPLETE paired old/upper Kpt record.
Consequently such a mismatch requires a missing old lower
Kpt socle entirely.

This is a local physical necessity, not a guarantee of zero
Bad cuts, a diary-uniform exceptional-node bound or BRD.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- On a true zero ordinary-graph-L finite numerical-H+ stage,
a candidate crossing that violates the unique old total
boring-step factor cannot share even its COMPLETE OLD cut
Kpt ancestor with ANY old live crossing source node.

The ZERO hypothesis is for ALL eligible genuine stage originals
and includes the actual symmetric graph relation; the full Kpt
ancestor retains dependent auxiliary E and all negative L data.
No new candidate AlgorithmRun or finite source enumeration. -/
theorem finiteNumericH_zero_stage_old_factor_mismatch_has_no_old_socle
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top cut : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hCut : cut < top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (D : MMap (normalizedKptSMTree family))
    (hFactor : R.F cut =
      MMap.comp (normalizedKptSMTree family)
        (R.F (cut+1)) D)
    (z : AdmissibleKptNode family)
    (hZ : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) Y)
    (hZCross : cut < LevelTree.lev z)
    (hMismatch :
      D (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)) ≠
        LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hZCross)) :
    ¬ ∃ w : AdmissibleKptNode family,
      w ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ (hWCross : cut < LevelTree.lev w),
        LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
          LevelTree.ancestor w cut (Nat.le_of_lt hWCross) := by
  rintro ⟨w,hW,hWCross,hOldEq⟩
  have hUpperCovered :=
    finiteNumericH_candidate_zero_column_old_socle_upper_covered
      family K k N hAvoid hSym U X Y hXY hY
      top R cut hZeroStage z w
      hZ hW hZCross hWCross hOldEq
  obtain ⟨u,hU,hZCut',hUCut,hUpperEq⟩ := hUpperCovered
  have hNoOldPair :=
    kpt_old_boring_factor_mismatch_has_no_old_full_pair
      family X top cut R hCut hBoring D hFactor
      z hZCross hMismatch
  apply hNoOldPair
  refine ⟨u,hU,hUCut,?_,?_⟩
  · have hLowerEq :=
      kpt_LevelTree_lower_ancestors_eq_of_higher_eq
        z u cut (cut+1) (by omega)
        (Nat.succ_le_iff.mpr hZCut')
        (Nat.succ_le_iff.mpr hUCut) hUpperEq
    simpa using hLowerEq
  · simpa using hUpperEq

end Kk
