import Kk.NumericHPhysicalNewRootRun
import Mathlib.Tactic

/-!
# Track C: original-ONLY new root seed regression

English proof and fourteen hostile checks were committed FIRST:
  docs/track_c_root_only_I1_regression_english_audit.md

The repaired new seed family is:
  Y = old genuine meet-and-selected-parameter closure
      UNION genuine NEW physical Kpt ORIGINAL nodes.

It does NOT insert their entire predecessor sets as initial seeds.
When every newly inserted physical original has the same E free
level top, every new-root seed has exactly LevelTree level top.
Consequently every lower-level I1 WITNESS IN THE INITIAL SEED
family comes from the OLD closure. This protects against the
prefix-saturation error separately formalized in Track C PR #183.

This says NOTHING about new level-p witnesses subsequently generated
in the actual AlgorithmRun's higher-selected-parameter closure,
nor about boringness or global bounded resolved diaries.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The new-root IMAGE in the corrected physical seed construction
consists of genuine original Kpt nodes of EXACTLY the stipulated
canonical E free level. This is not the full prefix pool. -/
theorem finiteNumericH_newRootOnly_seed_levels_exact
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (W : Set (Fin M))
    (top : Nat)
    (hEvery : ∀ w : Fin M, w ∈ W →
      (finiteNumericH L k M).freeLevel w.val = top) :
    ∀ z : AdmissibleKptNode family,
      z ∈ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W) →
      LevelTree.lev z = top := by
  intro z hz
  obtain ⟨w, hw, hEq⟩ := hz
  subst z
  change (finiteNumericH L k M).freeLevel w.val = top
  exact hEvery w hw

/-- Under equal actual top free levels of all newly seeded originals,
a lower-level I1 witness in the CORRECTED INITIAL SEED SET Y is
EXACTLY a witness already in the inherited old full closure.

The statement is only about the INITIAL seed set Y. Genuine
parameter closure in AlgorithmRun may still create new lower
I1 nodes, so no global boringness is asserted. -/
theorem finiteNumericH_rootOnly_lower_initial_I1_iff_old_closure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top p : Nat)
    (hBelow : p < top)
    (hEvery : ∀ w : Fin M, w ∈ W →
      (finiteNumericH L k M).freeLevel w.val = top) :
    (∃ z : AdmissibleKptNode family,
      z ∈ finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W ∧
      LevelTree.lev z = p) ↔
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) I X ∧
      LevelTree.lev z = p) := by
  constructor
  · rintro ⟨z,hY,hLevel⟩
    change z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) I X ∪
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W) at hY
    rcases hY with hOld | hNew
    · exact ⟨z,hOld,hLevel⟩
    · have hTop := finiteNumericH_newRootOnly_seed_levels_exact
        family L k M hAvoid W top hEvery z hNew
      omega
  · rintro ⟨z,hOld,hLevel⟩
    exact ⟨z,Or.inl hOld,hLevel⟩

#print axioms Kk.finiteNumericH_newRootOnly_seed_levels_exact
#print axioms Kk.finiteNumericH_rootOnly_lower_initial_I1_iff_old_closure

end Kk
