import Kk.TrackAOddIndexedStructuralBudget
import Kk.TrackGCrossingFrontier
import Mathlib.Tactic

/-!
# Track A/G: MAXIMAL odd old-boring lower-Kpt-socle witness per candidate

English proof and 17 adversarial checks committed FIRST:
 docs/track_a_odd_old_lower_socle_frontier_english_audit_20261122.md

Coverage of the genuine COMPLETE OLD dependent Kpt ancestor at a
higher cut persists at lower cuts of the SAME actual OLD AlgorithmRun.
The maximal LIVE odd old-boring crossing for EACH candidate index
therefore suffices for ALL its eligible cuts. This is weaker than
old-UPPER covering; it does not assume a target Y run or prove BRDs.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- An actual OLD live Kpt crossing w shares the full dependent
LOWER ancestor with fixed candidate z at cut. This notion is
strictly weaker than old-UPPER crossing pair coverage. -/
def kptOldLowerSocleCoveredAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family) (cut : Nat) : Prop :=
  ∃ (hz : cut < LevelTree.lev z),
    ∃ w : AdmissibleKptNode family,
      w ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ (hw : cut < LevelTree.lev w),
        LevelTree.ancestor z cut (Nat.le_of_lt hz) =
          LevelTree.ancestor w cut (Nat.le_of_lt hw)

/-- TRUE old-lower Kpt socle coverage is downward-monotone across
physical cuts of one actual OLD AlgorithmRun. The old source
closure grows downward, and equality of dependent high ancestors
implies equality at every lower level. No candidate run needed. -/
theorem kpt_old_lower_socle_covered_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (low high : Nat) (hLowHigh : low ≤ high) (hHigh : high < top)
    (hCovered : kptOldLowerSocleCoveredAt family X top R z high) :
    kptOldLowerSocleCoveredAt family X top R z low := by
  obtain ⟨hzHigh,w,hwLive,hwHigh,hEqHigh⟩ := hCovered
  have hzLow : low < LevelTree.lev z := by omega
  have hwLow : low < LevelTree.lev w := by omega
  refine ⟨hzLow,w,?_,hwLow,?_⟩
  · exact (kpt_actual_run_preCut_source_mono_down
      family X top low high R hLowHigh hHigh) hwLive
  · have hEqLow :=
      kpt_LevelTree_lower_ancestors_eq_of_higher_eq
        z w low high hLowHigh
        (Nat.le_of_lt hzHigh) (Nat.le_of_lt hwHigh) hEqHigh
    simpa using hEqLow

/-- All genuinely ODD, OLD-BORING, LIVE and crossing source
coordinates for one candidate Kpt node j. Different candidate
names can have distinct, non-interval eligible cut sets. -/
noncomputable def kptOddOldBoringCandidateCrossingCuts
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (j : Fin Q) : Finset Nat := by
  classical
  exact (Finset.range top).filter (fun cut =>
    cut % 2 = 1 ∧
    (¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X) cut) ∧
    live cut j = true ∧ cut < LevelTree.lev (node j))

/-- For ONE fixed candidate, a complete OLD lower Kpt socle
witness at its highest actual odd old-boring live crossing
suffices at ALL eligible odd cuts. Converse is by taking max.
The cut set need not be a chronological interval. -/
theorem kpt_odd_old_boring_lower_socle_covered_all_iff_max
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (j : Fin Q)
    (hNonempty : (kptOddOldBoringCandidateCrossingCuts
      family X top R node live j).Nonempty) :
    (∀ cut : Nat,
      cut ∈ kptOddOldBoringCandidateCrossingCuts
        family X top R node live j →
      kptOldLowerSocleCoveredAt family X top R (node j) cut) ↔
    kptOldLowerSocleCoveredAt family X top R (node j)
      ((kptOddOldBoringCandidateCrossingCuts
        family X top R node live j).max' hNonempty) := by
  let C := kptOddOldBoringCandidateCrossingCuts
    family X top R node live j
  constructor
  · intro hAll
    exact hAll _ (Finset.max'_mem C hNonempty)
  · intro hAtMax cut hCut
    have hMaxCut : C.max' hNonempty < top := by
      have hMem := Finset.max'_mem C hNonempty
      exact Finset.mem_range.mp (Finset.mem_filter.mp hMem).1
    have hLe : cut ≤ C.max' hNonempty :=
      Finset.le_max' C cut hCut
    exact kpt_old_lower_socle_covered_mono_down
      family X top R (node j) cut (C.max' hNonempty)
      hLe hMaxCut hAtMax

/-- ONE maximal complete old-lower ancestor witness for EACH
candidate source name removes ALL missing OLD lower-socle
obstructions at the truly ODD cuts that the old full Kpt run
regards as boring. No Y-run, no upper-cover assumption. -/
theorem kpt_odd_old_boring_no_missing_of_max_lower_socles
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (hMax : ∀ j : Fin Q,
      ∀ hNonempty : (kptOddOldBoringCandidateCrossingCuts
        family X top R node live j).Nonempty,
      kptOldLowerSocleCoveredAt family X top R (node j)
        ((kptOddOldBoringCandidateCrossingCuts
          family X top R node live j).max' hNonempty))
    (cut : Nat) (hCut : cut < top) (hOdd : cut % 2 = 1)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X) cut) :
    ¬ kptMissingOldSocleAt family X top R node live cut := by
  classical
  rintro ⟨j,hLive,hCross,hNoOld⟩
  let C := kptOddOldBoringCandidateCrossingCuts
    family X top R node live j
  have hMember : cut ∈ C := by
    unfold C kptOddOldBoringCandidateCrossingCuts
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hCut,
        ⟨hOdd,hBoring,hLive,hCross⟩⟩
  have hNonempty : C.Nonempty := ⟨cut,hMember⟩
  have hAtCut :=
    (kpt_odd_old_boring_lower_socle_covered_all_iff_max
      family X top R node live j hNonempty).mpr
        (hMax j hNonempty) cut hMember
  obtain ⟨hz,w,hw,hwCross,hEq⟩ := hAtCut
  exact hNoOld ⟨w,hw,hwCross,by simpa using hEq⟩

#print axioms Kk.kpt_old_lower_socle_covered_mono_down
#print axioms Kk.kpt_odd_old_boring_lower_socle_covered_all_iff_max
#print axioms Kk.kpt_odd_old_boring_no_missing_of_max_lower_socles

end Kk
