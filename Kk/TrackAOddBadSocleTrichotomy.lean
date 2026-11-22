import Kk.TrackGZeroStageExactBadTrichotomy
import Kk.NumericPrefixGapZero
import Mathlib.Tactic

/-!
# Track A/G: odd numerical-H exact Bad cuts have three physical witnesses

English FIRST and adversarial audit:
docs/track_a_odd_kpt_bad_socle_english_audit_20261122.md

This is the genuine odd-coordinate specialization of the independently
kernel-verified zero-L-stage factor-Bad trichotomy. All original stage
L bits are zero at odd coordinates, but auxiliary E can still cause
true terminal or missing-old-socle Kpt defects. No global BRD claim.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- Every odd numerical-H EXACT factor Bad cut forces a genuine
terminal I1, a same-component I2 meet, or a missing OLD COMPLETE
Kpt lower-ancestor source witness for a new crossing. No target
AlgorithmRun is postulated, and full E/B3 data is not discarded. -/
theorem finiteNumericH_odd_exact_bad_has_three_physical_witnesses
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
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
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (a : Nat)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ↔
      ∃ j : Fin Q, node j = z ∧ live (2*a+1) j = true)
    (hBad : (2*a+1) ∈ kptExactOldFactorBadCuts
      family X top R node live) :
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
      LevelTree.lev z = (2*a+1)) ∨
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
        SMTree.Envelope.SameComponent z w ∧
        LevelTree.lev (LevelTree.meet z w) = (2*a+1)) ∨
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I ((2*a+1)+1)) Y ∧
      ∃ (hZCross : (2*a+1) < LevelTree.lev z),
        ¬ ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I ((2*a+1)+1)) X ∧
          ∃ (hWCross : (2*a+1) < LevelTree.lev w),
            LevelTree.ancestor z (2*a+1) (Nat.le_of_lt hZCross) =
              LevelTree.ancestor w (2*a+1) (Nat.le_of_lt hWCross)) := by
  have hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I ((2*a+1)+1)) →
      (2*a+1)+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        (2*a+1) v.val (0 : Fin 1) = false := by
    intro v _ _
    change hNumericBinary K.binary k (2*a+1) v.val
      (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      K.binary k a v.val (0 : Fin 1)
  exact finiteNumericH_zero_stage_exact_factor_bad_has_three_physical_witnesses
    family K k N Q hAvoid hSym U X Y hXY hY
    top R node live (2*a+1) hExactY hZeroStage hBad

#print axioms Kk.finiteNumericH_odd_exact_bad_has_three_physical_witnesses

end Kk
