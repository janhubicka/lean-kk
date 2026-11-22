import Kk.TrackGOriginalSocleThresholds
import Kk.TrackEOriginalPrefixSocleIff
import Mathlib.Tactic

/-!
# Track G — bounded ORIGINAL-coordinate order-convex novelty carriers

English proof and hostile audit were committed FIRST:
docs/track_g_original_novelty_interval_carriers_english_audit_20261122.md

The previous node-based interval result G469 has up to Q
candidate Kpt node carriers (Q can depend on physical N).
G474 bounds the number of genuine ORIGINAL maximal socle tests
by |U| + |actual old selected levels|, independent of N.

We prove the actual ORIGINAL coordinate's full-source
socle-NOVEL support is also order-convex, and directly
derive an ACTIVE original novelty witness at each
nonstructural exact factor-Bad zero-graph-column cut.
Merely knowing that v belongs to the global test support
and is uncovered at cut does NOT establish activity at cut:
the proof must use E78's genuine equivalence to recover it.

These are interval CARRIERS, not a bound on the cardinality or
components of the actual Bad cut set. No uniform diary bound,
labelled inverse source orbit or global BRD theorem is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A genuine finite numerical-H+ ORIGINAL v is actively
OLD-SOCLE-NOVEL at one literal source cut when:
(1) v is in the actual selected stage-original pool,
(2) v represents a live candidate complete Kpt crossing
    of the cut, and
(3) the original's COMPLETE old Kpt ancestor has no old
    live source witness.

This uses the true old AlgorithmRun I tails and does not
assume any candidate Y AlgorithmRun or source index. -/
def KptOriginalSocleNovelAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin N) (cut : Nat) : Prop :=
  v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
  (∃ z : AdmissibleKptNode family,
    z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) Y ∧
    cut < LevelTree.lev z ∧
    z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) ∧
  ¬ KptActualOldSocleCoveredAt family X top R
    ((finiteNumericH K k N).kptOriginal family hAvoid v) cut

/-- For one real original v, its COMPLETE OLD Kpt socle-novel
candidate cuts form an order-convex interval, in literal
source coordinates < top.

Stage-original and candidate-source activity persist DOWN
the actual old scan; an old socle witness also persists
DOWN. Therefore failure of an old socle match persists
UP. No old-boring or zero-column premise is needed.

Intersecting this raw interval with old-boring/zero/Allowed
cut masks need NOT remain convex. -/
theorem kpt_original_active_socle_novel_order_convex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin N)
    (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c < top)
    (hNovelA : KptOriginalSocleNovelAt
      family K k N hAvoid U X Y top R v a)
    (hNovelC : KptOriginalSocleNovelAt
      family K k N hAvoid U X Y top R v c) :
    KptOriginalSocleNovelAt
      family K k N hAvoid U X Y top R v b := by
  obtain ⟨_hStageA,_hActiveA,hMissingA⟩ := hNovelA
  obtain ⟨hStageC,⟨z,hZC,hCrossC,hBelow⟩,_hMissingC⟩ := hNovelC
  have hLevels : R.I (c+1) ⊆ R.I (b+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (c+1) (by omega)] at hq
    rw [R.I_eq_final_tail_of_run (b+1) (by omega)]
    exact ⟨hq.1,by omega⟩
  have hStageB :
      v ∈ hStageOriginals K k N U (R.I (b+1)) :=
    (finiteNumericH_stageOriginals_mono_levels
      K k N U (R.I (c+1)) (R.I (b+1)) hLevels) hStageC
  have hZB :
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (b+1)) Y :=
    (kpt_oldRun_candidate_preCut_source_mono_down
      family X Y top b c R hbc hc) hZC
  refine ⟨hStageB, ⟨z,hZB,by omega,hBelow⟩,?_⟩
  intro hCoveredB
  apply hMissingA
  exact kpt_actual_old_socle_covered_mono_down
    family X top R
    ((finiteNumericH K k N).kptOriginal family hAvoid v)
    a b hab (by omega) hCoveredB

/-- If a single genuine NEW candidate crossing lacks an OLD
complete LOWER Kpt socle mate, then some ACTUALLY ACTIVE
numerical-H+ original at the SAME cut also has no old
complete prefix mate. This is not a consequence of merely
knowing a globally supported original is missing a mate;
it uses E78's true full candidate↔active original iff.

No zero-column, old-boring or Y-run hypothesis is needed. -/
theorem finiteNumericH_missing_candidate_socle_has_active_original
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (cut : Nat)
    (hMissing : ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      ¬ kpt_oldRun_node_lower_socle_covered
        family X top R z cut) :
    ∃ v : Fin N,
      KptOriginalSocleNovelAt
        family K k N hAvoid U X Y top R v cut := by
  classical
  obtain ⟨z,hZ,hCross,hNotCovered⟩ := hMissing
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
    obtain ⟨w,hW,hWCross,hEq⟩ :=
      hAllCandidate z hZ hCross
    exact hNotCovered ⟨w,hW,hCross,hWCross,hEq⟩
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
    intro hAll
    apply hNotAllCandidate
    exact (finiteNumericH_candidate_old_socle_iff_active_original_prefixes
      family K k N hAvoid U X Y hY top R cut).mpr hAll
  have hOne :
      ∃ v : Fin N,
        v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
        ActiveOriginal v ∧ ¬ OriginalCovered v := by
    by_contra hNone
    apply hNotAllOriginal
    intro v hStage hActive
    by_contra hMissingOriginal
    exact hNone ⟨v,hStage,hActive,hMissingOriginal⟩
  obtain ⟨v,hStage,hActive,hNotOld⟩ := hOne
  exact ⟨v,hStage,hActive,hNotOld⟩

/-- Stronger than merely G474's globally supported, uncovered
original: at one TRUE zero-graph-column, nonstructural exact
factor-Bad cut, there is an original v in the bounded E85
test support which is simultaneously ACTIVE and OLD-SOCLE-NOVEL
at THIS SAME cut.

Consequently all such Bad cuts can be charged to raw
order-convex original-coordinate novelty interval carriers,
number at most |U|+|actually selected old levels|.

NO bound on the NUMBER of Bad CUTS or interval lengths follows,
and intersecting each interval with old-boring/zero/Allowed can
split it. All source tests are complete dependent L+/E. -/
theorem finiteNumericH_zero_stage_exact_Bad_has_active_original_novel_carrier
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
      KptOriginalSocleNovelAt
        family K k N hAvoid U X Y top R v cut) ∧
    (kpt_originals_needing_max_old_socle_test
      family K k N hAvoid U X Y top R Allowed).card ≤
        U.card +
        (kpt_old_actual_selected_levels
          family X top R).card := by
  classical
  obtain ⟨j,_hLive,hNovel⟩ :=
    finiteNumericH_zero_stage_exact_bad_without_structural_has_socle_novel_index
      family K k N Q hAvoid hSym U X Y hXY hY top
      R node live cut hExactY hZeroStage hNoI1 hNoI2 hBad
  obtain ⟨hCross,hInY,hMissing⟩ := hNovel
  have hMissingCand :
      ∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ∧
        cut < LevelTree.lev z ∧
        ¬ kpt_oldRun_node_lower_socle_covered
          family X top R z cut :=
    ⟨node j,hInY,hCross,hMissing⟩
  obtain ⟨v,hStage,hActive,hMissingOriginal⟩ :=
    finiteNumericH_missing_candidate_socle_has_active_original
      family K k N hAvoid U X Y hY top R cut hMissingCand
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
  · exact ⟨v,hSupport,⟨hStage,hActive,hMissingOriginal⟩⟩
  · exact kpt_originals_needing_max_old_socle_test_card_le_root_add_selected
      family K k N hAvoid U X Y top R Allowed

end Kk
