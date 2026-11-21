import Kk.TrackEOldSocleOriginalMaxFrontier
import Mathlib.Tactic

/-!
# Track C: complete OLD Kpt prefix coverage is automatic from OLD seed prefixes

English proof and 18-case adversarial audit FIRST:
 docs/track_c_seed_prefix_old_socle_english_audit_20261121.md

A genuinely OLD initial Kpt seed x BELOW a physical original
O_v and STRICTLY ABOVE a source cut c witnesses the entire OLD
dependent Kpt c-ancestor of O_v, even when O_v itself is not in
the old source. The witness lies in the true pre-cut closure
under any AlgorithmRun tail simply because literal seeds survive.

This removes old-socle checking for originals already represented
by a sufficiently high OLD seed prefix. The source comparison is
literal and includes directed auxiliary E plus negative ordinary L;
no selected-age projection or source-index reverse map is used.

It does NOT prove that the actual resolved diary contains such
seed prefixes for every original or that physical zero-L/I1/I3
quietness follows without the remaining genuine stage geometry.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A full OLD Kpt seed prefix of a genuine physical original,
whose level is strictly above c. The source x is a literal seed,
not a guessed final source or graph-shadow representative. -/
def KptOriginalOldSeedPrefixAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (v : Fin M) (cut : Nat) : Prop :=
  ∃ x : AdmissibleKptNode family,
    x ∈ X ∧
      x ≤ (finiteNumericH L k M).kptOriginal family hAvoid v ∧
      cut < LevelTree.lev x

/-- ONE genuine old full-dependent seed prefix above c witnesses
the COMPLETE OLD Kpt ancestor of O_v at c in the actual old
pre-cut closure. No new-run, full source index, zero-column,
old-boring or numerical target root assumptions.

The level inequality is strict because E79 requires the OLD
witness to CROSS the cut; a seed ending at c is an I1 terminal,
not a crossing witness. -/
theorem kpt_actual_original_old_socle_covered_of_seed_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin M) (cut : Nat)
    (hSeed : KptOriginalOldSeedPrefixAt
      family L k M hAvoid X v cut) :
    KptActualOldSocleCoveredAt family X top Rold
      ((finiteNumericH L k M).kptOriginal family hAvoid v) cut := by
  obtain ⟨x,hX,hBelow,hCross⟩ := hSeed
  have hOriginalCross :
      cut < LevelTree.lev
        ((finiteNumericH L k M).kptOriginal family hAvoid v) :=
    lt_of_lt_of_le hCross (LevelTree.level_le_of_le hBelow)
  refine ⟨x, ?_, hOriginalCross, hCross, ?_⟩
  · exact (SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (Rold.I (cut+1)) X) hX
  · exact (LevelTree.eq_ancestor_of_le
      ((LevelTree.ancestor_le x cut
        (Nat.le_of_lt hCross)).trans hBelow)
      (LevelTree.level_ancestor x cut
        (Nat.le_of_lt hCross))
      (Nat.le_of_lt hOriginalCross)).symm

/-- ONE old seed prefix x below O_v and above the MAXIMAL
eligible source cut for v immediately discharges the exact
maximal complete OLD-socle premise of E79. Consequently E79
carries its FULL dependent prefix witness down to all
eligible lower cuts, even when those cuts are disconnected.

This criterion can omit many per-original maximal tests but
does not assert existence of high old seeds for the other v. -/
theorem kpt_actual_original_max_socle_of_seed_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (W : Finset (Fin M))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Allowed : Set Nat)
    (v : Fin M)
    (hNonempty :
      (kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).Nonempty)
    (hSeed : KptOriginalOldSeedPrefixAt
      family L k M hAvoid X v
      ((kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).max'
        hNonempty)) :
    KptActualOldSocleCoveredAt family X top Rold
      ((finiteNumericH L k M).kptOriginal family hAvoid v)
      ((kpt_actual_original_socle_allowed_cuts
        family L k M hAvoid W X Y top Rold Allowed v).max'
        hNonempty) :=
  kpt_actual_original_old_socle_covered_of_seed_prefix
    family L k M hAvoid X top Rold v _ hSeed

end Kk

#check @Kk.kpt_actual_original_old_socle_covered_of_seed_prefix
#print axioms Kk.kpt_actual_original_old_socle_covered_of_seed_prefix
#check @Kk.kpt_actual_original_max_socle_of_seed_prefix
#print axioms Kk.kpt_actual_original_max_socle_of_seed_prefix
