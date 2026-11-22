import Kk.TrackAOddIndexedStructuralBudget
import Kk.TrackEOldSocleOriginalMaxFrontier
import Mathlib.Tactic

/-!
# Track A/G: MAXIMAL old-Kpt-socle witness for odd old-boring candidate cuts

English/adversarial proof: docs/track_a_odd_old_lower_socle_frontier_english_audit_20261122.md

IMPORTANT duplicate-audit correction: generic COMPLETE OLD LOWER socle
coverage, its downward monotonicity and the arbitrary finite maximal-cut
iff were ALREADY verified in Track E E79
(Kk.TrackEOldSocleOriginalMaxFrontier). This module reuses those named
theorems, rather than duplicating them.

NEW: apply E79 to precisely odd OLD-BORING and LIVE candidate crossings,
then exclude missing complete OLD Kpt ancestors at every such cut and
bound TRUE ODD old-factor Bad cuts by Q+Q². No target Y run,
no upper source profile transfer, no global BRD assertion.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

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
      KptActualOldSocleCoveredAt family X top R (node j) cut) ↔
    KptActualOldSocleCoveredAt family X top R (node j)
      ((kptOddOldBoringCandidateCrossingCuts
        family X top R node live j).max' hNonempty) := by
  classical
  apply kpt_actual_old_socle_all_cuts_iff_max
    family X top R (node j)
    (kptOddOldBoringCandidateCrossingCuts
      family X top R node live j) ?_ hNonempty
  intro cut hCut
  exact Finset.mem_range.mp (Finset.mem_filter.mp hCut).1

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
      KptActualOldSocleCoveredAt family X top R (node j)
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
      KptActualOldSocleCoveredAt family X top R (node j)
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
#print axioms Kk.kpt_odd_old_boring_lower_socle_covered_all_iff_max
#print axioms Kk.kpt_odd_old_boring_no_missing_of_max_lower_socles

end Kk
