import Kk.TrackGCrossingFrontier
import Mathlib.Tactic

/-!
# Track G: every intrinsic physical Bad cut is terminal or lies
# on the verified one-node crossing-novelty interval of a genuine Kpt node.

English proof and adversarial audit, committed BEFORE Lean:
docs/track_g_badcut_interval_cover_english_audit_20261117.md

G278 gives an ACTUAL source node for every bad cut, with complete
old/upper dependent L+ ancestors from ONE node. G294 says that
each fixed node's true-run novel-crossing cuts form an interval.
We bridge G278's absent FULL physical pair to G294's existential
old-cover criterion, preserving genuine Kpt ancestor equalities.

This is a covering theorem, not a bound on interval number or
length, a per-diary event budget or a common labelled monoid orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A missing COMPLETE physical old/upper L+ pair of a NEW live node
cannot have an OLD source node with the same actual UPPER ancestor.
If such w existed its LOWER ancestor would match too, giving exactly
the missing pair on ONE old node and contradicting pair absence.

Uses the verified LevelTree ancestor restriction, not any false
prefix-closure hypothesis for the source itself. -/
theorem kpt_actual_missing_pair_forces_novel_cross
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (z : AdmissibleKptNode family) (cut : Nat)
    (p : PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd)
    (hz : cut < LevelTree.lev z)
    (hNewLive : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (Rnew.I (cut+1)) Y)
    (hOldAnc :
      (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hz)).val)
    (hUpperAnc :
      (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hz)).val)
    (hMissing :
      p ∉ FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I (cut+1)) X) cut) :
    kpt_actual_node_crossing_novel family X Y
      oldTop newTop Rold Rnew z cut := by
  classical
  refine ⟨hz,hNewLive,?_⟩
  intro hCovered
  obtain ⟨w,hOldLive,hZHigh,hWHigh,hEqUpper⟩ := hCovered
  have hEqLower :
      LevelTree.ancestor z cut (Nat.le_of_lt hZHigh) =
      LevelTree.ancestor w cut (Nat.le_of_lt hWHigh) :=
    kpt_LevelTree_lower_ancestors_eq_of_higher_eq
      z w cut (cut+1) (by omega)
      (Nat.succ_le_iff.mpr hZHigh)
      (Nat.succ_le_iff.mpr hWHigh) hEqUpper
  apply hMissing
  refine ⟨w,hOldLive,hWHigh,?_,?_⟩
  · exact hOldAnc.trans (congrArg Subtype.val hEqLower)
  · exact hUpperAnc.trans (congrArg Subtype.val hEqUpper)

/-- Any intrinsic bad cut of two genuine same-tree Kpt AlgorithmRuns
is explained by a true level-cut TERMINAL or by one actual NEW live
source node z whose full old/upper dependent L+ crossing pair lies
in a G294 single-node novelty INTERVAL.

This holds EVEN IF the larger AlgorithmRun did not select the cut.
The c<newTop bound is explicit; no equality or nestedness of the
old/new physical seed sets is postulated. No uniform counting. -/
theorem kpt_actual_bad_cut_terminal_or_novel_interval
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (cut : Nat) (hNewCut : cut < newTop)
    (hBad : cut ∈ kptPhysicalBadCuts family Rold.I oldTop
      (fun c => SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) X)
      (fun c => SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (c+1)) Y)) :
    cut < oldTop ∧ cut < newTop ∧ cut ∉ Rold.I cut ∧
      ∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (Rnew.I (cut+1)) Y ∧
        z ∉ SMTree.Envelope.closure (admissibleKptSTree family)
          (Rold.I (cut+1)) X ∧
        (LevelTree.lev z = cut ∨
          kpt_actual_node_crossing_novel family X Y
            oldTop newTop Rold Rnew z cut) := by
  classical
  obtain ⟨hOldCut,hBoring,hWitness⟩ :=
    kptPhysicalBadCut_has_novel_node_witness
      family Rold.I oldTop
      (fun c => SMTree.Envelope.closure (admissibleKptSTree family)
        (Rold.I (c+1)) X)
      (fun c => SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (c+1)) Y)
      cut hBad
  obtain ⟨z,hLive,hNotOld,hReason⟩ := hWitness
  refine ⟨hOldCut,hNewCut,hBoring,z,hLive,hNotOld,?_⟩
  rcases hReason with hTerminal | ⟨p,hPairMissing,hz,hOldAnc,hUpperAnc⟩
  · exact Or.inl hTerminal
  · exact Or.inr (kpt_actual_missing_pair_forces_novel_cross
      family X Y oldTop newTop Rold Rnew
      z cut p hz hLive hOldAnc hUpperAnc hPairMissing)

end Kk
