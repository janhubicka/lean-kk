import Kk.TrackGSocleNoveltyIntervals
import Kk.TrackEOriginalRepresentativeMaxFrontier
import Mathlib.Tactic

/-!
# Track G: charge genuine zero-column exact factor-Bad witnesses to
# ORIGINAL numerical-H+ Kpt nodes, not all auxiliary Kpt source names.

English-first proof and fourteen hostile checks:
docs/track_g_original_socle_threshold_english_audit_20261122.md

For one real old AlgorithmRun R, its full OLD lower-socle witnesses
persist downward in the source scan. Hence for a fixed ORIGINAL
node O, the raw cuts at which it has no old complete lower Kpt
socle form an UPPER final segment (within cut<top and cut<lev O).

If a candidate meet/parameter node z is below an actual original
O, a complete lower-socle mate of O also covers z. By contrapositive,
a missing old socle for z implies one for its representing original.

G469 and E71 combine to charge every TRUE zero ordinary graph-L
exact factor-Bad cut WITHOUT I1/I2 to a real stage original v : Fin N
with missing old full Kpt lower socle. This replaces potentially
huge auxiliary Kpt-node interval carriers by at most N ORIGINAL
coordinate carriers, but N is the growing physical stage size:
NO uniform diary event budget or BRD theorem is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- A full old LOWER Kpt socle mate of an original O also covers
any candidate Kpt source node z below O, provided z crosses cut.

The real old witness is LIVE in the actual pre-cut Kpt closure.
The original O itself need not be live there. -/
theorem kpt_oldRun_lower_socle_cover_transfer_from_original
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z original : AdmissibleKptNode family)
    (hBelow : z ≤ original)
    (cut : Nat) (hZCross : cut < LevelTree.lev z)
    (hOriginalCovered : kpt_oldRun_node_lower_socle_covered
      family X top R original cut) :
    kpt_oldRun_node_lower_socle_covered
      family X top R z cut := by
  obtain ⟨w,hWLive,hOriginalCross,hWCross,hOldEq⟩ :=
    hOriginalCovered
  have hZCut : cut ≤ LevelTree.lev z :=
    Nat.le_of_lt hZCross
  have hOriginalCut : cut ≤ LevelTree.lev original :=
    Nat.le_of_lt hOriginalCross
  have hZOriginalOld :
      LevelTree.ancestor z cut hZCut =
        LevelTree.ancestor original cut hOriginalCut := by
    exact LevelTree.eq_ancestor_of_le
      ((LevelTree.ancestor_le z cut hZCut).trans hBelow)
      (LevelTree.level_ancestor z cut hZCut)
      hOriginalCut
  exact ⟨w,hWLive,hZCross,hWCross,
    hZOriginalOld.trans hOldEq⟩

/-- The set of raw cut coordinates where an original lacks an
old complete lower Kpt socle is UPWARD CLOSED below its level
and the old scan top. This follows by contraposition of the
actual old source's downward persistence. No diary event bound. -/
theorem kpt_oldRun_missing_lower_socle_mono_up
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (original : AdmissibleKptNode family)
    (low high : Nat)
    (hLowHigh : low ≤ high) (hHigh : high < top)
    (hMissingLow : ¬ kpt_oldRun_node_lower_socle_covered
      family X top R original low) :
    ¬ kpt_oldRun_node_lower_socle_covered
      family X top R original high := by
  intro hCoveredHigh
  exact hMissingLow
    (kpt_oldRun_node_lower_socle_covered_mono_down
      family X top R original low high hLowHigh
      hHigh hCoveredHigh)

/-- For an exact complete candidate Kpt source inside ONE actual
finite numerical-H+ graph stage, every zero ordinary-L exact
factor-Bad cut with separately excluded I1 and I2 is witnessed
by an ACTUAL stage original v : Fin N having NO old complete
LOWER Kpt ancestor mate at the cut.

This is stronger than charging the cut to an auxiliary Kpt-node
source index: the original need not itself be a live source node.
Each original's missing-old-socle cuts have the upper-segment
property above. At most N original-coordinate interval CARRIERS,
not at most N Bad cuts, since each carrier can be arbitrarily long
and the physical N is not diary-uniform. -/
theorem finiteNumericH_zero_stage_exact_bad_has_original_missing_old_socle
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
    ∃ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
      cut < LevelTree.lev
        ((finiteNumericH K k N).kptOriginal family hAvoid v) ∧
      ¬ kpt_oldRun_node_lower_socle_covered
        family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        cut := by
  obtain ⟨j,_hLive,hNovel⟩ :=
    finiteNumericH_zero_stage_exact_bad_without_structural_has_socle_novel_index
      family K k N Q hAvoid hSym U X Y hXY hY top
      R node live cut hExactY hZeroStage hNoI1 hNoI2 hBad
  obtain ⟨hCross,hInY,hNoOldSocle⟩ := hNovel
  obtain ⟨v,hStage,hBelow⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U Y hY (R.I (cut+1))
      (node j) hInY
  have hOriginalCross : cut < LevelTree.lev
      ((finiteNumericH K k N).kptOriginal family hAvoid v) :=
    lt_of_lt_of_le hCross (LevelTree.level_le_of_le hBelow)
  refine ⟨v,hStage,hOriginalCross,?_⟩
  intro hOriginalCovered
  exact hNoOldSocle
    (kpt_oldRun_lower_socle_cover_transfer_from_original
      family X top R (node j)
      ((finiteNumericH K k N).kptOriginal family hAvoid v)
      hBelow cut hCross hOriginalCovered)

end Kk
