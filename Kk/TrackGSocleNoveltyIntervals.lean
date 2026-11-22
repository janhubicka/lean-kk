import Kk.TrackGZeroStageExactBadTrichotomy
import Kk.TrackGCrossingFrontier
import Mathlib.Tactic

/-!
# Track G: intervals of old FULL Kpt lower-socle novelty

English-first proof and 15 hostile checks:
docs/track_g_old_socle_novelty_interval_english_audit_20261122.md

Use ONE old genuine AlgorithmRun R on X, and candidate new source
closure(S,R.I(cut+1),Y), without a target run on Y. The source grows
as the old scan descends. If a candidate crossing has an old LIVE
source node with the same complete LOWER Kpt ancestor at a high
cut, it retains an old socle mate at every lower cut.

Consequently, for one fixed candidate node z, its old-socle-novel
cuts form an order-convex interval in the raw source coordinates.

At a TRUE zero ordinary-L graph stage, G449 says any exact old-factor
Bad cut is a terminal, I2 meet, or missing old Kpt socle witness.
If terminal and meet events are independently excluded, the Bad
cut belongs to a novelty interval of some actual live target index.

This yields at most Q NODE-INTERVAL CARRIERS for a fixed complete
finite candidate index of size Q, but DOES NOT bound the length
of those intervals, the cardinality/components of the Bad set,
or Q uniformly in the diary. No labelled inverse-source orbit
or sharp Kk-free BRD theorem is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- The complete candidate pre-cut Kpt closure on Y is monotone
as the source cut descends along the OLD actual run R on X.
This does not assume an actual AlgorithmRun on Y. -/
theorem kpt_oldRun_candidate_preCut_source_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hLowHigh : low ≤ high) (hHigh : high < top) :
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (high+1)) Y ⊆
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (low+1)) Y := by
  have hLevel : R.I (high+1) ⊆ R.I (low+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (high+1) (by omega)] at hq
    rw [R.I_eq_final_tail_of_run (low+1) (by omega)]
    exact ⟨hq.1,
      le_trans (Nat.add_le_add_right hLowHigh 1) hq.2⟩
  exact envelope_closure_mono_seeds_and_levels
    (admissibleKptSTree family)
    (R.I (high+1)) (R.I (low+1)) Y Y hLevel
    (by intro z hz; exact hz)

/-- The fixed candidate node z has a complete OLD LOWER-socle mate
at cut if some genuine old LIVE crossing w shares its literal
level-cut Kpt ancestor with z.

This is a weaker relation than matching the complete paired
old/upper crossing, but retains ALL dependent L+/E data in
the lower Kpt ancestor. -/
def kpt_oldRun_node_lower_socle_covered
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family) (cut : Nat) : Prop :=
  ∃ w : AdmissibleKptNode family,
    w ∈ SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X ∧
    ∃ (hz : cut < LevelTree.lev z)
      (hw : cut < LevelTree.lev w),
      LevelTree.ancestor z cut (Nat.le_of_lt hz) =
        LevelTree.ancestor w cut (Nat.le_of_lt hw)

/-- A real old FULL lower-socle witness at high persists at low:
the actual old pre-cut source only grows downward, and equality
of higher Kpt ancestors restricts to lower ancestors. -/
theorem kpt_oldRun_node_lower_socle_covered_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (low high : Nat)
    (hLowHigh : low ≤ high) (hHigh : high < top)
    (hCovered : kpt_oldRun_node_lower_socle_covered
      family X top R z high) :
    kpt_oldRun_node_lower_socle_covered
      family X top R z low := by
  obtain ⟨w,hWLive,hZHigh,hWHigh,hEqHigh⟩ := hCovered
  have hZLow : low < LevelTree.lev z := by omega
  have hWLow : low < LevelTree.lev w := by omega
  refine ⟨w, ?_, hZLow,hWLow, ?_⟩
  · exact (kpt_actual_run_preCut_source_mono_down
      family X top low high R hLowHigh hHigh) hWLive
  · exact kpt_LevelTree_lower_ancestors_eq_of_higher_eq
      z w low high hLowHigh (Nat.le_of_lt hZHigh)
      (Nat.le_of_lt hWHigh) hEqHigh

/-- A candidate node z is physically OLD-SOCLE NOVEL at a cut:
it is live in the complete target closure over the old I tail,
crosses the cut and has no old live source with its complete
LOWER Kpt ancestor. No target AlgorithmRun is needed. -/
def kpt_oldRun_candidate_node_socle_novel
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family) (cut : Nat) : Prop :=
  cut < LevelTree.lev z ∧
    z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) Y ∧
    ¬ kpt_oldRun_node_lower_socle_covered family X top R z cut

/-- The OLD-SOCLE NOVEL cuts of a fixed candidate node form an
order-convex interval in the old run's actual raw source cut
coordinates. Intersecting the interval with the set of old-boring
or zero-column cuts can split its support; no event-count bound. -/
theorem kpt_oldRun_candidate_node_socle_novel_order_convex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c < top)
    (hNovelA : kpt_oldRun_candidate_node_socle_novel
      family X Y top R z a)
    (hNovelC : kpt_oldRun_candidate_node_socle_novel
      family X Y top R z c) :
    kpt_oldRun_candidate_node_socle_novel
      family X Y top R z b := by
  obtain ⟨_hALevel,_hALive,hANotCovered⟩ := hNovelA
  obtain ⟨hCLevel,hCLive,_hCNotCovered⟩ := hNovelC
  have hBLive :
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (b+1)) Y :=
    (kpt_oldRun_candidate_preCut_source_mono_down
      family X Y top b c R hbc hc) hCLive
  refine ⟨by omega,hBLive,?_⟩
  intro hCoveredB
  exact hANotCovered
    (kpt_oldRun_node_lower_socle_covered_mono_down
      family X top R z a b hab (by omega) hCoveredB)

/-- At one TRUE zero ordinary graph-L candidate stage, if all
new terminal I1 and genuine same-component I2 meet events are
separately excluded, each exact factor-Bad cut has a LIVE target
index in the physical old-socle novelty interval of its Kpt node.

Together with the order-convex theorem this gives a cover by at
most Q candidate-node interval CARRIERS (for a finite index Q).
It does not bound the number of actual Bad cuts in each carrier. -/
theorem finiteNumericH_zero_stage_exact_bad_without_structural_has_socle_novel_index
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
    (cut : Nat)
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
    ∃ j : Fin Q,
      live cut j = true ∧
      kpt_oldRun_candidate_node_socle_novel
        family X Y top R (node j) cut := by
  have hCases :=
    finiteNumericH_zero_stage_exact_factor_bad_has_three_physical_witnesses
      family K k N Q hAvoid hSym U X Y hXY hY top
      R node live cut hExactY hZeroStage hBad
  rcases hCases with hTerminal | hMeet | hMissing
  · exact False.elim (hNoI1 hTerminal)
  · exact False.elim (hNoI2 hMeet)
  · obtain ⟨z,hZ,hCross,hNoOld⟩ := hMissing
    obtain ⟨j,hName,hLive⟩ := (hExactY z).mp hZ
    subst z
    refine ⟨j,hLive,hCross,hZ,?_⟩
    rintro ⟨w,hW,hZCross',hWCross,hOldEq⟩
    apply hNoOld
    exact ⟨w,hW,hWCross,by simpa using hOldEq⟩

end Kk
