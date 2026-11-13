import Kk.B3AmbientPoolSocle
import SuccessorTree.V10.I3AlgorithmInterestingBridge
import Mathlib.Tactic

/-!
# Track B: a genuine I3 event hides a concrete extra upper original

English-first argument and hostile audit:
  docs/track_b_actual_i3_extra_upper_english_audit.md

The full prescribed I3 crossing is the selected-original pool
representing ACTUAL closure nodes, not every ambient cut-eligible name.
One missing full upper L-reduct in a B3 discrepancy has an actual
original-name witness in that selected pool.

This is a necessary diagnostic for a real AlgorithmRun I3 event;
nothing about global diary orbit uniqueness or actual finite exact
big Ramsey degrees is inferred.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Source profiles restricted to two chosen original-name predicates
have automatically matching old ordinary-L socles in a COMMON
ambient A, whenever the marked pool has a genuinely eligible name.

Chosen target representatives can differ from supplied marked w:
the proof uses the exact `source_original` theorem on both sides. -/
theorem selectedStagePool_full_to_marked_Lsocle_coverage
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Full Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val) :
    ∀ S, S ∈ (selectedStagePoolPrescribedData A cut original Full).source →
      ∃ T, T ∈ (selectedStagePoolPrescribedData A cut original Marked).source ∧
        SameInitialL
          (prescribedOrdinarySocle
            ((selectedStagePoolPrescribedData A cut original Full).target S))
          (prescribedOrdinarySocle
            ((selectedStagePoolPrescribedData A cut original Marked).target T)) cut := by
  classical
  intro S hS
  obtain ⟨v,_hFull,_hFree,_hOld,hFullTarget⟩ :=
    selectedStagePoolPrescribedData_source_original A cut original Full S hS
  let T : PartialTypeWithE cut db du dd :=
    A.partialTypeAt cut (original w).val
  have hT : T ∈ (selectedStagePoolPrescribedData A cut original Marked).source := by
    change ∃ u : Fin M,
      (Marked u ∧ cut+1 ≤ A.freeLevel (original u).val) ∧
        A.partialTypeAt cut (original u).val = T
    exact ⟨w,⟨hw,hwCut⟩,rfl⟩
  obtain ⟨u,_hMarked,_hFreeMarked,_hOldMarked,hMarkedTarget⟩ :=
    selectedStagePoolPrescribedData_source_original A cut original Marked T hT
  refine ⟨T,hT,?_⟩
  rw [hFullTarget,hMarkedTarget]
  have hMarkedSocle : SameInitialL
      (prescribedOrdinarySocle
        (A.partialTypeAt (cut+1) (original u).val)) A.L cut :=
    ambient_partialType_prescribedSocle A cut (original u).val hCut
  have hReverse : SameInitialL A.L
      (prescribedOrdinarySocle
        (A.partialTypeAt (cut+1) (original u).val)) cut := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      exact (hMarkedSocle.1 x hx).symm
    · intro x y hx hy t
      exact (hMarkedSocle.2.1 x y hx hy t).symm
    · intro x hx t
      exact (hMarkedSocle.2.2.1 x hx t).symm
    · intro x hx t
      exact (hMarkedSocle.2.2.2 x hx t).symm
  exact (ambient_partialType_prescribedSocle
    A cut (original v).val hCut).trans hReverse

/-- A failed FULL corrected B3 test and a passing marked test
of two true selected-stage original-name pools force an actual
Full-selected original with an upper ordinary-L type missing from
the marked prescribed profile.

This conclusion is stronger than an abstract missing type: it
identifies an original NAME in the actual full source selection. -/
theorem selectedStagePool_fullB3_failure_has_extra_original
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Full Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData A cut original Full).CorrectedB3 family)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    ∃ v : Fin M,
      Full v ∧ cut+1 ≤ A.freeLevel (original v).val ∧
      ¬ (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType
        ((A.partialTypeAt (cut+1) (original v).val).lReduct) := by
  classical
  let F : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut original Full
  let G : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut original Marked
  have hSocle : ∀ S, S ∈ F.source →
      ∃ T, T ∈ G.source ∧
        SameInitialL
          (prescribedOrdinarySocle (F.target S))
          (prescribedOrdinarySocle (G.target T)) cut :=
    selectedStagePool_full_to_marked_Lsocle_coverage
      A cut hCut original Full Marked w hw hwCut
  obtain ⟨U,hUpper,hMissing⟩ :=
    fullB3_failure_good_marked_missing_upper
      F G family hSocle hFailure hMarked
  obtain ⟨S,hS,hUEq⟩ := hUpper
  obtain ⟨v,hFull,hFree,_hOld,hTarget⟩ :=
    selectedStagePoolPrescribedData_source_original A cut original Full S hS
  have hActual : U =
      (A.partialTypeAt (cut+1) (original v).val).lReduct := by
    calc
      U = (F.target S).lReduct := hUEq
      _ = (A.partialTypeAt (cut+1) (original v).val).lReduct :=
        congrArg (fun T : PartialTypeWithE (cut+1) db du dd => T.lReduct)
          hTarget
  refine ⟨v,hFull,hFree,?_⟩
  intro hAllowed
  rw [hActual] at hMissing
  exact hMissing hAllowed

/-- A genuinely interesting non-structural I3 crossing of the REAL
closure Z cannot be invisible to a B3-good marked finite original
pool unless some FULL selected original has a missing upper L type.

All nontrivial I3 assumptions are explicit: positive cut, actual
finite original pool for Z, absence of both structural I1 and I2,
and the actual IsInterestingAt predicate for that Z. -/
theorem represented_nonstructural_I3_has_extra_upper_original
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (cut : Nat) (hPositive : 0 < cut) (hCut : cut < A.size)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hInteresting :
      SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family) Z cut)
    (Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    ∃ v : Fin M,
      closureSelectedOriginal family A hAvoid original Z cut v ∧
      cut+1 ≤ A.freeLevel (original v).val ∧
      ¬ (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType
        ((A.partialTypeAt (cut+1) (original v).val).lReduct) := by
  have hFailure :
      ¬ (selectedStagePoolPrescribedData A cut original
        (closureSelectedOriginal family A hAvoid original Z cut)).CorrectedB3
          family := by
    exact algorithmI3_failsCorrectedB3
      family A hAvoid original Z hPool cut hPositive
      hNoI1 hNoI2 hInteresting
  exact selectedStagePool_fullB3_failure_has_extra_original
    family A cut hCut original
    (closureSelectedOriginal family A hAvoid original Z cut)
    Marked w hw hwCut hFailure hMarked

/-- An ACTUAL AlgorithmRun selection at cut, when neither I1 nor
I2 can explain it, has an extra original upper type not seen by any
eligible B3-good marked profile.

The stage is the genuine pre-cut closure at R.I (cut+1); its
interestingness is derived from R, not postulated. -/
theorem algorithmRun_nonstructural_I3_has_extra_upper_original
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPositive : 0 < cut)
    (hBelow : cut < top) (hCut : cut < A.size)
    (hSelected : cut ∈ R.I 0)
    (hPool : ∀ z, z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    ∃ v : Fin M,
      closureSelectedOriginal family A hAvoid original
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut v ∧
      cut+1 ≤ A.freeLevel (original v).val ∧
      ¬ (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType
        ((A.partialTypeAt (cut+1) (original v).val).lReduct) := by
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) X
  have hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z cut := by
    have hFinal := R.finalLevel_interesting_of_run hTopSeed hSelected
    have hNext := R.I_succ_eq_higher_final_of_run cut hBelow
    simpa only [Z,hNext] using hFinal
  exact represented_nonstructural_I3_has_extra_upper_original
    family A hAvoid original Z hPool cut hPositive hCut
    hNoI1 hNoI2 hInteresting Marked w hw hwCut hMarked

#print axioms selectedStagePool_full_to_marked_Lsocle_coverage
#print axioms selectedStagePool_fullB3_failure_has_extra_original
#print axioms represented_nonstructural_I3_has_extra_upper_original
#print axioms algorithmRun_nonstructural_I3_has_extra_upper_original

end Kk
