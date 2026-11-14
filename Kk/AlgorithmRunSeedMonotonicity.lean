import Kk.NumericHNewRootClosureAbsorption
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track C: actual AlgorithmRun interesting levels MONOTONE in initial Kpt seeds

English mathematical proof and twenty hostile checks committed FIRST:
  docs/track_c_algorithmRun_seed_monotonicity_english_audit.md

For the verified successor-tree I1/I2/I3 decision, making the
complete Kpt node set LARGER cannot destroy interestingness:
  I1/I2 witness persists;
  I3 impossibility of a one-level skipping map on the small
  crossing family persists on the larger crossing family.

Consequently two ACTUAL AlgorithmRuns on X ⊆ Y with identical
top height and SMTree satisfy R_X.I i ⊆ R_Y.I i for EVERY i≤top.
This is proved directly by descending Algorithm 5.4 recursion;
no arbitrary interesting-level monotonicity hypothesis is assumed.

When corrected physical next seeds Y are the full inherited closure
over the OLD run's true selected levels plus genuine NEW original Kpt
nodes, X⊆Y gives retention of the old SAME-HEIGHT selected levels.
Combining this with the exact old-closure absorption theorem gives
IDENTICAL actual new-run pre-cut Kpt sets at cuts strictly BELOW
every old selected level, if bare old+new actual originals are used.

No claim across DIFFERENT scan heights, no false boringness of K4
auxiliary microevents and no cross-occurrence labelled source orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- The EXACT successor-tree Algorithm 5.4 interestingness test
(I1, I2, or impossibility of a one-level skip realizing every
crossing) is monotone under increasing the COMPLETE Kpt node set.

In the I3 branch, a map realizing all crossings in the larger
set would realize all in the smaller set, contradicting I3.
We are not asserting monotonicity of a guessed ordinary-L B3 age
test independently of the real successor-tree construction. -/
theorem envelope_IsInterestingAt_mono_nodes
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (C D : Set T)
    (hCD : C ⊆ D) (i : Nat)
    (hInteresting : SMTree.Envelope.IsInterestingAt H C i) :
    SMTree.Envelope.IsInterestingAt H D i := by
  rcases hInteresting with ⟨x,hx,hLev⟩ | hOther
  · exact Or.inl ⟨x,hCD hx,hLev⟩
  · rcases hOther with hMeet | hNoMap
    · obtain ⟨a,ha,b,hb,hComp,hLev⟩ := hMeet
      exact Or.inr (Or.inl
        ⟨a,hCD ha,b,hCD hb,hComp,hLev⟩)
    · right
      right
      intro hMap
      obtain ⟨F,hSkip,hCross⟩ := hMap
      apply hNoMap
      refine ⟨F,hSkip,?_⟩
      intro z hz hzi
      exact hCross (hCD hz) hzi

/-- Genuine meet/selected-parameter Kpt closure is monotone
simultaneously in the seed-set and selected-level arguments.
No false distributivity of closure over union is used. -/
theorem envelope_closure_mono_seeds_and_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (I J : Set Nat) (X Y : Set T)
    (hIJ : I ⊆ J) (hXY : X ⊆ Y) :
    SMTree.Envelope.closure S I X ⊆
      SMTree.Envelope.closure S J Y := by
  apply SMTree.Envelope.closure_minimal
    S I X (SMTree.Envelope.closure S J Y)
  · intro z hz
    exact (SMTree.Envelope.subset_closure S J Y) (hXY hz)
  · exact SMTree.Envelope.closure_meetClosed S J Y
  · exact (SMTree.Envelope.closure_parameterClosed
      S J Y).mono_levels hIJ

/-- Main same-height seed monotonicity theorem for TWO TRUE
AlgorithmRuns R on X and Q on Y. If X⊆Y, then at EVERY scanned
level i the selected level-set of R is included in Q's.

This is derived by genuine downward AlgorithmRun recursion and
the exact IsInterestingAt trichotomy, including I3. We do not
assume the two runs made identical monoid choices, or even that
their selected level-sets agree. No one-level E1 axiom is added.
-/
theorem envelope_algorithmRun_selected_levels_mono_seeds
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    {S : STree T Label}
    (H : SMTree S)
    (X Y : Set T)
    (hXY : X ⊆ Y)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun H X top)
    (Q : SMTree.Envelope.AlgorithmRun H Y top) :
    ∀ i : Nat, i ≤ top → R.I i ⊆ Q.I i := by
  apply induction_down
  · rw [R.topI, Q.topI]
  · intro i hi hNext
    have hClosure :
        SMTree.Envelope.closure S (R.I (i+1)) X ⊆
          SMTree.Envelope.closure S (Q.I (i+1)) Y :=
      envelope_closure_mono_seeds_and_levels
        S (R.I (i+1)) (Q.I (i+1)) X Y hNext hXY
    by_cases hInteresting :
        SMTree.Envelope.IsInterestingAt H
          (SMTree.Envelope.closure S (R.I (i+1)) X) i
    · have hInterestingQ :
          SMTree.Envelope.IsInterestingAt H
            (SMTree.Envelope.closure S (Q.I (i+1)) Y) i :=
        envelope_IsInterestingAt_mono_nodes H
          (SMTree.Envelope.closure S (R.I (i+1)) X)
          (SMTree.Envelope.closure S (Q.I (i+1)) Y)
          hClosure i hInteresting
      have hRI := (R.interesting_step i hi hInteresting).1
      have hQI := (Q.interesting_step i hi hInterestingQ).1
      rw [hRI,hQI]
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hEq | hOld
      · exact Set.mem_insert_iff.mpr (Or.inl hEq)
      · exact Set.mem_insert_iff.mpr (Or.inr (hNext hOld))
    · obtain ⟨_,_,_,hRI,_⟩ :=
        R.noninteresting_step i hi hInteresting
      have hQNext : Q.I (i+1) ⊆ Q.I i := by
        rcases Q.level_step i hi with hQI | hQI
        · rw [hQI]
        · rw [hQI]
          intro z hz
          exact Set.mem_insert_of_mem hz
      rw [hRI]
      exact hNext.trans hQNext

/-- At the SAME scan height, enlarging actual Kpt seeds X to the
REPAIRED new-root seed family Y constructed from the OLD run's
genuine selected levels I=Rold.I0 retains EVERY old selected level.

This DISCHARGES the previous hypothetical retention assumption
under its exact same-height premise. The old closure is full
Kpt meet-and-parameter closure, not selected-front ordinary L.
-/
theorem finiteNumericH_newRoot_run_retains_same_height_old_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid (Rold.I 0) X W) top) :
    Rold.I 0 ⊆ Rnew.I 0 := by
  have hSeeds :
      X ⊆ finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid (Rold.I 0) X W := by
    intro z hz
    exact Or.inl
      ((SMTree.Envelope.subset_closure
        (admissibleKptSTree family) (Rold.I 0) X) hz)
  exact envelope_algorithmRun_selected_levels_mono_seeds
    (normalizedKptSMTree family)
    X (finiteNumericH_physicalExtendedSeeds
      family L k M hAvoid (Rold.I 0) X W)
    hSeeds top Rold Rnew 0 (Nat.zero_le top)

/-- At a REAL new-root cut STRICTLY below every selected level of
the SAME-HEIGHT old AlgorithmRun, the corrected full old-closure
seed family has EXACTLY the same actual new-run pre-cut closure
as the bare original-only family X ∪ image(new physical originals).

The old run's selected-level retention is now a THEOREM from
seed-monotonicity, not an independent hRetained hypothesis.
Therefore every I1/I2 and full OLD/UPPER dependent L+ source
event of these two pre-cut node sets also agrees literally.

This does not compare a prior run on a SHORTER top height,
and does not guarantee the tested cut is below old minimum I.
-/
theorem finiteNumericH_newRoot_preCut_absorbs_retained_old_run
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid (Rold.I 0) X W) top)
    (cut : Nat) (hCut : cut < top)
    (hAbove : ∀ q : Nat, q ∈ Rold.I 0 → cut < q) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rnew.I (cut+1))
      (finiteNumericH_physicalExtendedSeeds family L k M
        hAvoid (Rold.I 0) X W) =
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Rnew.I (cut+1)) (X ∪ O) := by
  have hRetained : Rold.I 0 ⊆ Rnew.I 0 :=
    finiteNumericH_newRoot_run_retains_same_height_old_levels
      family L k M hAvoid X W top Rold Rnew
  exact finiteNumericH_newRoot_run_preCut_absorbs_of_retained_above
    family L k M hAvoid (Rold.I 0) X W top Rnew
    cut hCut hRetained hAbove

#print axioms Kk.envelope_IsInterestingAt_mono_nodes
#print axioms Kk.envelope_closure_mono_seeds_and_levels
#print axioms Kk.envelope_algorithmRun_selected_levels_mono_seeds
#print axioms Kk.finiteNumericH_newRoot_run_retains_same_height_old_levels
#print axioms Kk.finiteNumericH_newRoot_preCut_absorbs_retained_old_run

end Kk
