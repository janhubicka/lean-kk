import Kk.TrackGSocleNoveltyIntervals
import Kk.TrackEOriginalPrefixSocleIff
import Kk.TrackESelectedLevelOriginalBudget
import Mathlib.Tactic

/-!
# Track G: charge exact zero-column factor-Bad cuts to a bounded set
# of ACTUAL numerical-H+ ORIGINAL Kpt prefix tests, not auxiliary names.

English proof and 16 hostile checks committed FIRST:
docs/track_g_original_socle_threshold_english_audit_20261122.md

Crucial adversarial simplification: Track E E78 already proved
candidate-old-Kpt-socle matching IFF all genuinely active ORIGINAL
representatives have old complete prefixes. E79 already proved
downward persistence/maximal original cut tests, and E86 bounds
their total number by |U| + |ACTUAL selected OLD levels|, independent
of the physical new carrier size N.

The genuinely NEW result here connects G469/G449's TRUE zero-column
exact-factor-Bad missing-old-socle witness to that E86 bounded set
of original-coordinate maximal tests, rather than adding duplicate
monotonicity and ancestor-transfer proofs.

The number of bad cuts per original can still be large, selected
old levels may depend on the diary resolution, and neither common
labelled inverse-source orbit nor sharp Kk-free BRD is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A TRUE zero ordinary-L finite numerical-H+ exact factor-Bad
cut without new terminal I1 or actual same-component meet I2
has a MISSING COMPLETE OLD Kpt prefix at some genuinely ACTIVE
original v. That original is in the E85 finite maximal-prefix
test support restricted to any Allowed cut mask containing cut.

The number of original tests in that support is at most
  |U| + |kpt_old_actual_selected_levels family X top R|,
INDEPENDENT of the new numerical-H+ carrier N and the potentially
much larger auxiliary complete Kpt candidate source index Q.

This bounds original test CARRIERS, NOT bad-cut cardinality,
exceptional interval lengths, or the count of selected levels
by a fixed diary. All dependent old L+/E ancestor data remain.
-/
theorem finiteNumericH_zero_stage_exact_Bad_charged_to_bounded_originals
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
    (Allowed : Set Nat)
    (cut : Nat) (hAllowed : cut ∈ Allowed)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ↔
      ∃ j : Fin Q, node j = z ∧ live cut j = true)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ∧
        SMTree.Envelope.SameComponent z w ∧
        LevelTree.lev (LevelTree.meet z w) = cut)
    (hBad : cut ∈ kptExactOldFactorBadCuts
      family X top R node live) :
    (∃ v : Fin N,
      v ∈ kpt_originals_needing_max_old_socle_test
        family K k N hAvoid U X Y top R Allowed ∧
      ¬ KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v) cut) ∧
    (kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed).card ≤
      U.card +
        (kpt_old_actual_selected_levels family X top R).card := by
  classical
  obtain ⟨j,_hLive,hNovel⟩ :=
    finiteNumericH_zero_stage_exact_bad_without_structural_has_socle_novel_index
      family K k N Q hAvoid hSym U X Y hXY hY top
      R node live cut hExactY hZeroStage hNoI1 hNoI2 hBad
  obtain ⟨hCross,hInY,hMissing⟩ := hNovel
  have hNotAllCandidate :
      ¬ (∀ (z : AdmissibleKptNode family),
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y →
        ∀ (hZCross : cut < LevelTree.lev z),
          ∃ w : AdmissibleKptNode family,
            w ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            ∃ (hWCross : cut < LevelTree.lev w),
              LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
                LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) := by
    intro hAllCandidate
    apply hMissing
    obtain ⟨w,hw,hWCross,hEq⟩ :=
      hAllCandidate (node j) hInY hCross
    exact ⟨w,hw,hCross,hWCross,hEq⟩
  let ActiveOriginal (v : Fin N) : Prop :=
    ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v
  let OriginalCovered (v : Fin N) : Prop :=
    KptActualOldSocleCoveredAt family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v) cut
  have hNotAllOriginal :
      ¬ (∀ v : Fin N,
        v ∈ hStageOriginals K k N U (R.I (cut+1)) →
        ActiveOriginal v → OriginalCovered v) := by
    intro hAllOriginal
    have hAllOriginal' :
        (∀ v : Fin N,
          v ∈ hStageOriginals K k N U (R.I (cut+1)) →
          (∃ z : AdmissibleKptNode family,
            z ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) Y ∧
            cut < LevelTree.lev z ∧
            z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) →
          ∃ w : AdmissibleKptNode family,
            w ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            ∃ (hV : cut < LevelTree.lev
              ((finiteNumericH K k N).kptOriginal family hAvoid v))
              (hW : cut < LevelTree.lev w),
              LevelTree.ancestor
                ((finiteNumericH K k N).kptOriginal family hAvoid v)
                cut (Nat.le_of_lt hV) =
              LevelTree.ancestor w cut (Nat.le_of_lt hW)) := by
      intro v hv hActive
      exact hAllOriginal v hv hActive
    have hAllCand :=
      (finiteNumericH_candidate_old_socle_iff_active_original_prefixes
        family K k N hAvoid U X Y hY top R cut).mpr hAllOriginal'
    exact hNotAllCandidate hAllCand
  have hExistsOriginal :
      ∃ v : Fin N,
        v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
        ActiveOriginal v ∧ ¬ OriginalCovered v := by
    by_contra hNone
    apply hNotAllOriginal
    intro v hStage hActive
    by_contra hMissingOriginal
    exact hNone ⟨v,hStage,hActive,hMissingOriginal⟩
  obtain ⟨v,hStage,hActive,hMissingOriginal⟩ := hExistsOriginal
  obtain ⟨hCut,hOldBoring,_hBadFactor⟩ :=
    (mem_kptExactOldFactorBadCuts
      family X top R node live cut).mp hBad
  have hCandidateCut :
      cut ∈ kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v :=
    (mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v cut).mpr
      ⟨hCut,hOldBoring,hStage,hActive⟩
  have hAllowedCut :
      cut ∈ kpt_actual_original_socle_allowed_cuts
        family K k N hAvoid U X Y top R Allowed v :=
    (mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mpr
      ⟨hCandidateCut,hAllowed⟩
  have hSupport :
      v ∈ kpt_originals_needing_max_old_socle_test
        family K k N hAvoid U X Y top R Allowed :=
    (mem_kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed v).mpr
        ⟨cut,hAllowedCut⟩
  constructor
  · exact ⟨v,hSupport,hMissingOriginal⟩
  · exact kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U X Y top R Allowed

end Kk
