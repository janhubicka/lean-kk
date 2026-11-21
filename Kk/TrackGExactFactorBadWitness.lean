import Kk.TrackGExactFactorBadCuts
import Mathlib.Tactic

/-!
# Track G: every exact finite factor-Bad cut has a genuine
# terminal, meet, or UNIQUE-old-factor crossing mismatch witness.

English proof and 14 hostile checks committed FIRST:
docs/track_g_exact_factor_bad_witness_english_audit_20261121.md

This is a finite physical witness extraction, not a bound on the
number of such witnesses or cuts. A mismatch of the original total
factor cannot share its COMPLETE paired old/upper Kpt ancestor
record with any crossing of the old pre-cut source. Negative
ordinary L and auxiliary dependent E are not projected away.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- At an exact factor-Bad cut of the ORIGINAL genuine Kpt run,
choose its actual skip-only old total factor D. A single
indexed full-source terminal, a pair with genuine I2 meet,
or one indexed full Kpt crossing DISAGREEING with D must exist.

No index injectivity, source orbit or no-I2 assumption. The
factor D is genuine, exists by old boringness, and is uniquely
determined by the total old F endpoints. -/
theorem kpt_exact_factor_bad_has_terminal_meet_or_mismatch
    {db du dd Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (cut : Nat)
    (hBad : cut ∈ kptExactOldFactorBadCuts
      family X top RX node live) :
    ∃ D : MMap (normalizedKptSMTree family),
      D.map.SkipsOnly cut ∧
      RX.F cut = MMap.comp (normalizedKptSMTree family)
        (RX.F (cut+1)) D ∧
      ((∃ j : Fin Q, live cut j = true ∧
          LevelTree.lev (node j) = cut) ∨
       (∃ j k : Fin Q, live cut j = true ∧
          live cut k = true ∧
          SMTree.Envelope.SameComponent (node j) (node k) ∧
          LevelTree.lev (LevelTree.meet (node j) (node k)) = cut) ∨
       (∃ j : Fin Q, live cut j = true ∧
          ∃ (hCross : cut < LevelTree.lev (node j)),
            D (LevelTree.ancestor (node j) cut
                (Nat.le_of_lt hCross)) ≠
              LevelTree.ancestor (node j) (cut+1)
                (Nat.succ_le_iff.mpr hCross))) := by
  classical
  obtain ⟨hCut,hOldBoring,hNotCompat⟩ :=
    (mem_kptExactOldFactorBadCuts
      family X top RX node live cut).mp hBad
  obtain ⟨D,hSkipD,_hOldCross,_hOldI,hFactorD⟩ :=
    RX.noninteresting_step cut hCut hOldBoring
  refine ⟨D,hSkipD,hFactorD,?_⟩
  by_contra hNoWitness
  apply hNotCompat
  refine ⟨?_,?_,?_⟩
  · intro j hLive hLevel
    apply hNoWitness
    exact Or.inl ⟨j,hLive,hLevel⟩
  · intro j k hLiveJ hLiveK hMeet
    apply hNoWitness
    exact Or.inr (Or.inl
      ⟨j,k,hLiveJ,hLiveK,hMeet.1,hMeet.2⟩)
  · intro E hFactorE j hLive hCross
    have hED : E = D :=
      kpt_MMap_comp_left_cancel
        (normalizedKptSMTree family)
        (RX.F (cut+1)) E D
        (hFactorE.symm.trans hFactorD)
    by_contra hMismatch
    apply hNoWitness
    refine Or.inr (Or.inr ⟨j,hLive,hCross,?_⟩)
    simpa only [hED] using hMismatch

/-- A violation of the UNIQUE old skip factor on a candidate
crossing cannot be represented by ANY genuinely old crossing
with the exact SAME lower AND upper Kpt ancestors.

In particular it is not merely an ordinary-L mismatch:
the complete dependent L+/E ancestor PAIR is novel.
The candidate node need not itself be a new FINAL source node;
an old-final name newly activated at this pre-cut stage is allowed. -/
theorem kpt_old_boring_factor_mismatch_has_no_old_full_pair
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top cut : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hCut : cut < top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RX.I (cut+1)) X) cut)
    (D : MMap (normalizedKptSMTree family))
    (hFactor : RX.F cut =
      MMap.comp (normalizedKptSMTree family)
        (RX.F (cut+1)) D)
    (z : AdmissibleKptNode family)
    (hZCross : cut < LevelTree.lev z)
    (hMismatch :
      D (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)) ≠
        LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hZCross)) :
    ¬ ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RX.I (cut+1)) X ∧
        ∃ (hWCross : cut < LevelTree.lev w),
          LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
            LevelTree.ancestor w cut (Nat.le_of_lt hWCross) ∧
          LevelTree.ancestor z (cut+1)
            (Nat.succ_le_iff.mpr hZCross) =
            LevelTree.ancestor w (cut+1)
              (Nat.succ_le_iff.mpr hWCross) := by
  obtain ⟨E,_hSkipE,hOldCross,_hI,hFactorE⟩ :=
    RX.noninteresting_step cut hCut hBoring
  have hDE : D = E :=
    kpt_MMap_comp_left_cancel
      (normalizedKptSMTree family) (RX.F (cut+1)) D E
      (hFactor.symm.trans hFactorE)
  rintro ⟨w,hw,hWCross,hEqOld,hEqUpper⟩
  apply hMismatch
  calc
    D (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)) =
      E (LevelTree.ancestor z cut (Nat.le_of_lt hZCross)) := by
        rw [hDE]
    _ = E (LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) := by
      rw [hEqOld]
    _ = LevelTree.ancestor w (cut+1)
          (Nat.succ_le_iff.mpr hWCross) := hOldCross hw hWCross
    _ = LevelTree.ancestor z (cut+1)
          (Nat.succ_le_iff.mpr hZCross) := hEqUpper.symm

end Kk
