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


/-- True odd OLD-factor Bad cuts are confined to Q terminal levels
and Q² pair-meet levels if every actual candidate source name has
a complete OLD LOWER Kpt-ancestor witness at just its HIGHEST
old-boring odd live crossing cut (when one exists).
Even missing socles at OTHER, non-boring cuts are allowed:
we eliminate the missing branch only WHERE the Bad test applies. -/
theorem finiteNumericH_odd_bad_card_le_of_max_lower_socles
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
    (hExactY : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ↔
        ∃ i : Fin Q, node i = z ∧ live cut i = true)
    (hMax : ∀ j : Fin Q,
      ∀ hNonempty : (kptOddOldBoringCandidateCrossingCuts
        family X top R node live j).Nonempty,
      kptOldLowerSocleCoveredAt family X top R (node j)
        ((kptOddOldBoringCandidateCrossingCuts
          family X top R node live j).max' hNonempty)) :
    (kptOddExactBadCuts family X top R node live).card ≤
      Q + Q*Q := by
  classical
  have hAll :=
    finiteNumericH_odd_bad_subset_structural_union_missing
      family K k N Q hAvoid hSym U X Y hXY hY
      top R node live hExactY
  have hSub : kptOddExactBadCuts family X top R node live ⊆
      kptIndexedStructuralLevels family node := by
    intro cut hBadOdd
    rcases Finset.mem_union.mp (hAll hBadOdd) with hStruct | hMissing
    · exact hStruct
    · have hBad : cut ∈ kptExactOldFactorBadCuts
          family X top R node live :=
        (Finset.mem_filter.mp hBadOdd).2
      obtain ⟨hCut,hBoring,_⟩ :=
        (mem_kptExactOldFactorBadCuts
          family X top R node live cut).mp hBad
      have hMissingCuts : cut ∈
          (Finset.range top).filter (fun cut =>
            cut % 2 = 1 ∧
              kptMissingOldSocleAt family X top R node live cut) :=
        hMissing
      obtain ⟨_,hOdd,hMissingWitness⟩ :=
        (Finset.mem_filter.mp hMissingCuts)
      exact False.elim
        ((kpt_odd_old_boring_no_missing_of_max_lower_socles
          family X top R node live hMax cut hCut hOdd hBoring)
          hMissingWitness)
  have hCard := Finset.card_le_card hSub
  have hBound := kpt_indexed_structural_levels_card_le family node
  omega

#print axioms Kk.finiteNumericH_odd_bad_card_le_of_max_lower_socles
#print axioms Kk.kpt_old_lower_socle_covered_mono_down
#print axioms Kk.kpt_odd_old_boring_lower_socle_covered_all_iff_max
#print axioms Kk.kpt_odd_old_boring_no_missing_of_max_lower_socles

end Kk
