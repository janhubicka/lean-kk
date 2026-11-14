import Kk.NumericHPhysicalNewRootRun
import Kk.NumericHStructuralCutClassifier
import Kk.FullPhysicalCrossingRelation
import SuccessorTree.Envelope
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track C: eliminate redundant inherited Kpt closure at genuine new-root pre-cuts

English-first proof and eighteen adversarial checks:
  docs/track_c_new_root_closure_absorption_english_audit.md

The REPAIRED physical new-root seed family from merged Track C PR #165 is
  Y = closure_I(X) UNION {actual NEW original Kpt nodes}.

The old closure has already introduced parameters using old selected
levels I. If a newly tested pre-cut level set J CONTAINS I, then
the complete meet/selected-parameter closure of Y over J is EXACTLY
the complete closure over J of the smaller original-only seed
family X UNION {new original Kpt nodes}.

Unlike the initial-seed-only I1 regression, this is an identity of
ACTUAL later pre-cut Kpt closures, hence of their complete I1/I2
event predicates and full OLD/UPPER dependent L+ crossing relation.
It uses closure minimality and parameter level monotonicity,
NOT a false distributivity of closure over arbitrary unions.

The inclusion I⊆J is indispensable; this theorem does NOT
prove old interesting levels survive the new-root extension or
that no new meet/parameter microevents are generated.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- GENERAL absorption of a prior parameter-and-meet closure into
a later closure whose selected levels include all the prior levels.
Neither union distributivity nor downward closure is postulated.

If I is NOT contained in J, old generated parameter nodes can be
visible as preinserted seeds even when the new J-closure of X∪O
would not generate them, so the assumption is mathematically real. -/
theorem envelope_closure_absorbs_old_closure_of_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label) (I J : Set Nat)
    (X O : Set T) (hIJ : I ⊆ J) :
    SMTree.Envelope.closure S J
      (SMTree.Envelope.closure S I X ∪ O) =
    SMTree.Envelope.closure S J (X ∪ O) := by
  apply Set.Subset.antisymm
  · have hOld :
        SMTree.Envelope.closure S I X ⊆
          SMTree.Envelope.closure S J (X ∪ O) := by
      apply SMTree.Envelope.closure_minimal S I X
        (SMTree.Envelope.closure S J (X ∪ O))
      · intro x hx
        exact (SMTree.Envelope.subset_closure S J (X ∪ O))
          (Or.inl hx)
      · exact SMTree.Envelope.closure_meetClosed S J (X ∪ O)
      · exact
          (SMTree.Envelope.closure_parameterClosed
            S J (X ∪ O)).mono_levels hIJ
    have hUnion :
        SMTree.Envelope.closure S I X ∪ O ⊆
          SMTree.Envelope.closure S J (X ∪ O) := by
      intro x hx
      rcases hx with hxOld | hxNew
      · exact hOld hxOld
      · exact (SMTree.Envelope.subset_closure S J (X ∪ O))
          (Or.inr hxNew)
    exact SMTree.Envelope.closure_minimal
      S J (SMTree.Envelope.closure S I X ∪ O)
      (SMTree.Envelope.closure S J (X ∪ O))
      hUnion
      (SMTree.Envelope.closure_meetClosed S J (X ∪ O))
      (SMTree.Envelope.closure_parameterClosed S J (X ∪ O))
  · have hSeeds :
        X ∪ O ⊆
          SMTree.Envelope.closure S J
            (SMTree.Envelope.closure S I X ∪ O) := by
      intro x hx
      apply SMTree.Envelope.subset_closure S J
        (SMTree.Envelope.closure S I X ∪ O)
      rcases hx with hxOld | hxNew
      · exact Or.inl
          ((SMTree.Envelope.subset_closure S I X) hxOld)
      · exact Or.inr hxNew
    exact SMTree.Envelope.closure_minimal
      S J (X ∪ O)
      (SMTree.Envelope.closure S J
        (SMTree.Envelope.closure S I X ∪ O))
      hSeeds
      (SMTree.Envelope.closure_meetClosed S J
        (SMTree.Envelope.closure S I X ∪ O))
      (SMTree.Envelope.closure_parameterClosed S J
        (SMTree.Envelope.closure S I X ∪ O))

/-- In the actual physical finite numerical H+ Kpt structure,
the repaired next seed family has been defined as the full OLD
selected closure plus ONLY the NEW original nodes, not all their
proper prefixes.

Whenever J contains the inherited selected set I, taking the
true meet-and-parameter closure over J ABSORBS the old closure:
the result is exactly the one generated from bare X plus new
physical Kpt originals. This is an identity of full dependent
L+ admissible Kpt node sets, not an L-only graph shadow. -/
theorem finiteNumericH_newRoot_closure_absorption
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I J : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (hIJ : I ⊆ J) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    SMTree.Envelope.closure (admissibleKptSTree family) J
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) =
    SMTree.Envelope.closure (admissibleKptSTree family) J
      (X ∪ O) := by
  change
    SMTree.Envelope.closure (admissibleKptSTree family) J
      (SMTree.Envelope.closure (admissibleKptSTree family) I X ∪
        ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) =
    SMTree.Envelope.closure (admissibleKptSTree family) J
      (X ∪ ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
  exact envelope_closure_absorbs_old_closure_of_levels
    (admissibleKptSTree family) I J X
    ((fun w : Fin M =>
      (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    hIJ

/-- At a REAL pre-cut of a corrected actual new-root AlgorithmRun,
if the inherited levels I were selected among the HIGHER levels,
the entire pre-cut meet/parameter closure agrees with the closure
of bare old ORIGINAL seeds and new ORIGINAL Kpt nodes.

Therefore I1, I2 and the ENTIRE canonical physical old/upper
L+ crossing relation agree ON THE NOSE at that cut, including
I2 forks and auxiliary negative/E atoms. No corrected B3 or
no-I2 premise is smuggled into this data-level identity. -/
theorem finiteNumericH_newRoot_run_preCut_structural_profile_absorbs
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) top)
    (cut : Nat) (hCut : cut < top)
    (hRetainedHigher : I ⊆ R.I (cut+1)) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Zfull : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds family L k M
          hAvoid I X W)
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) (X ∪ O)
    (KptI1AtCut family Zfull cut ↔ KptI1AtCut family Zbare cut) ∧
    (KptI2MeetAtCut family Zfull cut ↔
      KptI2MeetAtCut family Zbare cut) ∧
    FullPhysicalClosureCrossing family Zfull cut =
      FullPhysicalClosureCrossing family Zbare cut := by
  have hEq :
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W) =
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (X ∪ ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) :=
    finiteNumericH_newRoot_closure_absorption
      family L k M hAvoid I (R.I (cut+1)) X W
      hRetainedHigher
  dsimp only
  rw [hEq]
  exact ⟨Iff.rfl,Iff.rfl,rfl⟩

/-- The needed old-level inclusion at a REAL new-root pre-cut
follows from two explicit diary requirements:
  (i) the old selected levels I are still selected by this new run,
  (ii) all these inherited levels lie STRICTLY above the tested cut.

The proven AlgorithmRun final-tail identity gives precisely
I⊆R.I(cut+1), so the full generated pre-cut closure is equal
to the smaller bare old+new ORIGINAL-seed closure.

Do NOT infer retention of old selected I from this theorem;
interesting-level persistence across DIFFERENT seed sets remains
a separate mathematical obligation. -/
theorem finiteNumericH_newRoot_run_preCut_absorbs_of_retained_above
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) top)
    (cut : Nat) (hCut : cut < top)
    (hRetained : I ⊆ R.I 0)
    (hAbove : ∀ q : Nat, q ∈ I → cut < q) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W) =
    SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) (X ∪ O) := by
  have hLevels : I ⊆ R.I (cut+1) := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)]
    exact ⟨hRetained hq, Nat.succ_le_iff.mpr (hAbove q hq)⟩
  exact finiteNumericH_newRoot_closure_absorption
    family L k M hAvoid I (R.I (cut+1)) X W hLevels

#print axioms Kk.envelope_closure_absorbs_old_closure_of_levels
#print axioms Kk.finiteNumericH_newRoot_closure_absorption
#print axioms Kk.finiteNumericH_newRoot_run_preCut_structural_profile_absorbs
#print axioms Kk.finiteNumericH_newRoot_run_preCut_absorbs_of_retained_above

end Kk
