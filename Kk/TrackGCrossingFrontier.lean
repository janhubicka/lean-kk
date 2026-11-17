import Kk.TrackGBadCutNovelNodeWitness
import Mathlib.Tactic

/-!
# Track G: one-node physical Kpt crossing novelty has interval support

English proof and adversarial checks were committed FIRST:
  docs/track_g_single_node_crossing_frontier_english_audit_20261117.md

The source test is the FULL actual Kpt ancestor at the UPPER
cut+1, not an ordinary-L graph-age projection. Equality of the
upper Kpt ancestor forces equality of ALL lower Kpt ancestors,
including dependent E and negative L atoms.

For one fixed node z and two genuine AlgorithmRuns, the cuts where
z is live in the new pre-cut closure but its complete old/upper
crossing has no physical old pre-cut realization form an INTERVAL.
This does NOT bound its length, the number of actual source nodes,
or the union of their novelty intervals; old-boring intersections
may split the interval. No diary-uniform source orbit/BRD is proved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Equality of a HIGHER actual ancestor of two nodes forces equality
of any LOWER actual ancestor. Proof via LevelTree uniqueness, rather
than an assumed (nonexistent) ancestor_ancestor lemma. -/
theorem kpt_LevelTree_lower_ancestors_eq_of_higher_eq
    {T : Type*} [PartialOrder T] [LevelTree T]
    (a b : T) (low high : Nat) (hLowHigh : low ≤ high)
    (ha : high ≤ LevelTree.lev a)
    (hb : high ≤ LevelTree.lev b)
    (hEq : LevelTree.ancestor a high ha =
      LevelTree.ancestor b high hb) :
    LevelTree.ancestor a low (le_trans hLowHigh ha) =
      LevelTree.ancestor b low (le_trans hLowHigh hb) := by
  let upper : T := LevelTree.ancestor a high ha
  have hUpperA : upper ≤ a := LevelTree.ancestor_le a high ha
  have hUpperB : upper ≤ b := by
    dsimp [upper]
    rw [hEq]
    exact LevelTree.ancestor_le b high hb
  have hLowerUpper : low ≤ LevelTree.lev upper := by
    simpa only [upper, LevelTree.level_ancestor] using hLowHigh
  let lower : T := LevelTree.ancestor upper low hLowerUpper
  have hLowerLeUpper : lower ≤ upper :=
    LevelTree.ancestor_le upper low hLowerUpper
  have hLowerLevel : LevelTree.lev lower = low :=
    LevelTree.level_ancestor upper low hLowerUpper
  have hLowerA :
      lower = LevelTree.ancestor a low (le_trans hLowHigh ha) :=
    LevelTree.eq_ancestor_of_le
      (le_trans hLowerLeUpper hUpperA) hLowerLevel
      (le_trans hLowHigh ha)
  have hLowerB :
      lower = LevelTree.ancestor b low (le_trans hLowHigh hb) :=
    LevelTree.eq_ancestor_of_le
      (le_trans hLowerLeUpper hUpperB) hLowerLevel
      (le_trans hLowHigh hb)
  exact hLowerA.symm.trans hLowerB

/-- True pre-cut Kpt parameter-closed sources grow as the scan cut
moves DOWN. The AlgorithmRun level sets are genuine final tails.
This is NOT true for arbitrary unrelated per-cut source families. -/
theorem kpt_actual_run_preCut_source_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top low high : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hLowHigh : low ≤ high) (hHigh : high < top) :
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (high+1)) X ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (low+1)) X := by
  have hLevel : R.I (high+1) ⊆ R.I (low+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (high+1) (by omega)] at hq
    rw [R.I_eq_final_tail_of_run (low+1) (by omega)]
    exact ⟨hq.1, by omega⟩
  exact envelope_closure_mono_seeds_and_levels
    (admissibleKptSTree family)
    (R.I (high+1)) (R.I (low+1)) X X hLevel
    (by intro x hx; exact hx)

/-- A fixed source node z has an old COMPLETE crossing-pair cover at
cut precisely when SOME old live Kpt source node w shares the actual
upper (cut+1) Kpt ancestor with z. This already forces the lower
cut ancestor pair to agree, not merely the two marginal type sets. -/
def kpt_actual_run_node_upper_covered
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
      LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hz) =
        LevelTree.ancestor w (cut+1) (Nat.succ_le_iff.mpr hw)

/-- A genuine old crossing cover persists at every LOWER source
cut: old live closure only increases and the actual Kpt ancestor
equalities restrict to lower levels. -/
theorem kpt_actual_run_node_upper_covered_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (low high : Nat)
    (hLowHigh : low ≤ high) (hHigh : high < top)
    (hCovered : kpt_actual_run_node_upper_covered
      family X top R z high) :
    kpt_actual_run_node_upper_covered
      family X top R z low := by
  obtain ⟨w,hwLive,hZHigh,hWHigh,hEqHigh⟩ := hCovered
  have hZLow : low < LevelTree.lev z := by omega
  have hWLow : low < LevelTree.lev w := by omega
  refine ⟨w, ?_, hZLow,hWLow, ?_⟩
  · exact (kpt_actual_run_preCut_source_mono_down
      family X top low high R hLowHigh hHigh) hwLive
  · exact kpt_LevelTree_lower_ancestors_eq_of_higher_eq
      z w (low+1) (high+1) (by omega)
      (Nat.succ_le_iff.mpr hZHigh)
      (Nat.succ_le_iff.mpr hWHigh) hEqHigh

/-- The node z contributes a PHYSICAL novel crossing at cut when
it is an actual live NEW source node above the cut but NO old
physical source node realizes the same complete old/upper Kpt pair. -/
def kpt_actual_node_crossing_novel
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (z : AdmissibleKptNode family) (cut : Nat) : Prop :=
  cut < LevelTree.lev z ∧
    z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
      (Rnew.I (cut+1)) Y ∧
    ¬ kpt_actual_run_node_upper_covered family X oldTop Rold z cut

/-- For ONE FIXED z the actual physical novel-crossing cuts form
an interval in the common Kpt SOURCE coordinates (possibly empty).
No interval-length bound, common labelled orbit, arbitrary-diary
f or uniform exceptional-level count is inferred. -/
theorem kpt_actual_node_crossing_novel_order_convex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (z : AdmissibleKptNode family)
    (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (hcOld : c < oldTop) (hcNew : c < newTop)
    (hNovelA : kpt_actual_node_crossing_novel
      family X Y oldTop newTop Rold Rnew z a)
    (hNovelC : kpt_actual_node_crossing_novel
      family X Y oldTop newTop Rold Rnew z c) :
    kpt_actual_node_crossing_novel
      family X Y oldTop newTop Rold Rnew z b := by
  obtain ⟨_hALevel,_hALive,hANotCovered⟩ := hNovelA
  obtain ⟨hCLevel,hCLive,_hCNotCovered⟩ := hNovelC
  have hBLive :
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (b+1)) Y :=
    (kpt_actual_run_preCut_source_mono_down
      family Y newTop b c Rnew hbc hcNew) hCLive
  refine ⟨by omega, hBLive, ?_⟩
  intro hCoveredB
  exact hANotCovered
    (kpt_actual_run_node_upper_covered_mono_down
      family X oldTop Rold z a b hab (by omega) hCoveredB)

end Kk
