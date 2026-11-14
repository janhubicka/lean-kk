import Kk.B3UpperProfileSufficiency
import Mathlib.Tactic

/-!
# Track B: ordinary-L B3 comparison across DIFFERENT actual ambients

English-first proof and adversarial audit:
  docs/track_b_cross_ambient_cutstar_english_audit.md

Unlike the previous same-ambient Track B lemmas, A and B can be two
different enumerated partial structures with unrelated original-name
pools. At one COMMON source cut, agreement of their complete old
ordinary L socles plus inclusion of their COMPLETE next-cut ordinary
L reducts suffices for corrected B3 transfer.

The crucial old-socle coverage is PROVED from source originality
and the upper-type inclusion, with no artificial nonempty witness.
Thus the empty-source case is genuinely included.

Nothing here compares the auxiliary E records, different cut ranks,
a full labelled monoid orbit, or the unbounded resolved diary.
-/

namespace Kk

open SuccessorTree.V10

/-- Reversal of all four parts of the exact old ordinary-L socle
relation: carrier, every directed binary, unary and diagonal atom. -/
theorem crossAmbient_sameInitialL_reverse
    {db du dd : Nat} {A B : AgeTestModel db du dd}
    {cut : Nat} (h : SameInitialL A B cut) :
    SameInitialL B A cut := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    exact (h.1 x hx).symm
  · intro x y hx hy t
    exact (h.2.1 x y hx hy t).symm
  · intro x hx t
    exact (h.2.2.1 x hx t).symm
  · intro x hx t
    exact (h.2.2.2 x hx t).symm

/-- One-sided complete upper-L-reduct inclusion between two
genuinely selected original pools from DIFFERENT actual ambient
structures forces complete OLD L-socle coverage.

A source S of the left profile provides its chosen upper type R.
Inclusion supplies an actual right source T; both chosen targets
are represented by eligible physical originals. Align their old
socles through the displayed same-initial-L hypothesis.

In particular, there is no standalone nonempty-right-profile
assumption: it follows from upper inclusion when the left source
is nonempty. -/
theorem selectedStagePool_crossAmbient_socle_coverage_of_upperL
    {db du dd M₁ M₂ : Nat}
    (A B : EnumeratedPartialStructure db du dd)
    (cut : Nat)
    (hCutA : cut < A.size) (hCutB : cut < B.size)
    (originalA : Fin M₁ → Fin A.size)
    (originalB : Fin M₂ → Fin B.size)
    (SelectedA : Fin M₁ → Prop)
    (SelectedB : Fin M₂ → Prop)
    (hCommon : SameInitialL A.L B.L cut)
    (hUpper : ∀ R,
      (selectedStagePoolPrescribedData A cut originalA SelectedA).PrescribedUpperLType R →
      (selectedStagePoolPrescribedData B cut originalB SelectedB).PrescribedUpperLType R) :
    ∀ S,
      S ∈ (selectedStagePoolPrescribedData A cut originalA SelectedA).source →
      ∃ T,
        T ∈ (selectedStagePoolPrescribedData B cut originalB SelectedB).source ∧
        SameInitialL
          (prescribedOrdinarySocle
            ((selectedStagePoolPrescribedData A cut originalA SelectedA).target S))
          (prescribedOrdinarySocle
            ((selectedStagePoolPrescribedData B cut originalB SelectedB).target T))
          cut := by
  classical
  let F : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut originalA SelectedA
  let G : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData B cut originalB SelectedB
  intro S hS
  have hR : F.PrescribedUpperLType (F.target S).lReduct := by
    exact ⟨S,hS,rfl⟩
  obtain ⟨T,hT,_hType⟩ := hUpper (F.target S).lReduct hR
  obtain ⟨v,_hv,_hFree,_hOld,hTargetA⟩ :=
    selectedStagePoolPrescribedData_source_original
      A cut originalA SelectedA S hS
  obtain ⟨w,_hw,_hFreeB,_hOldB,hTargetB⟩ :=
    selectedStagePoolPrescribedData_source_original
      B cut originalB SelectedB T hT
  have hSocleA : SameInitialL
      (prescribedOrdinarySocle (F.target S)) A.L cut := by
    rw [hTargetA]
    exact ambient_partialType_prescribedSocle
      A cut (originalA v).val hCutA
  have hSocleB : SameInitialL
      (prescribedOrdinarySocle (G.target T)) B.L cut := by
    rw [hTargetB]
    exact ambient_partialType_prescribedSocle
      B cut (originalB w).val hCutB
  refine ⟨T,hT,?_⟩
  exact (hSocleA.trans hCommon).trans
    (crossAmbient_sameInitialL_reverse hSocleB)

/-- Complete right-to-left corrected B3 transfer between TWO
different genuine ambient original-name pools. Matching old L
socles is a real hypothesis, but separate source coverage
is DERIVED from one-sided upper-L inclusion. -/
theorem selectedStagePool_crossAmbient_B3_of_upperL
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A B : EnumeratedPartialStructure db du dd)
    (cut : Nat)
    (hCutA : cut < A.size) (hCutB : cut < B.size)
    (originalA : Fin M₁ → Fin A.size)
    (originalB : Fin M₂ → Fin B.size)
    (SelectedA : Fin M₁ → Prop)
    (SelectedB : Fin M₂ → Prop)
    (hCommon : SameInitialL A.L B.L cut)
    (hUpper : ∀ R,
      (selectedStagePoolPrescribedData A cut originalA SelectedA).PrescribedUpperLType R →
      (selectedStagePoolPrescribedData B cut originalB SelectedB).PrescribedUpperLType R)
    (hB :
      (selectedStagePoolPrescribedData B cut originalB SelectedB).CorrectedB3 family) :
    (selectedStagePoolPrescribedData A cut originalA SelectedA).CorrectedB3 family := by
  exact correctedB3_of_Lprofile_dominance
    (selectedStagePoolPrescribedData A cut originalA SelectedA)
    (selectedStagePoolPrescribedData B cut originalB SelectedB)
    family
    (selectedStagePool_crossAmbient_socle_coverage_of_upperL
      A B cut hCutA hCutB originalA originalB
      SelectedA SelectedB hCommon hUpper)
    hUpper hB

/-- Even across two distinct ambients, equality of complete permitted
upper ordinary-L reduct profiles and equality of the old ordinary-L
socle imply EQUIVALENCE of corrected B3 tests.

The result includes empty selected pools without any fabricated
source, anchor, default original or target type. -/
theorem selectedStagePool_crossAmbient_B3_iff_equal_upperL
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A B : EnumeratedPartialStructure db du dd)
    (cut : Nat)
    (hCutA : cut < A.size) (hCutB : cut < B.size)
    (originalA : Fin M₁ → Fin A.size)
    (originalB : Fin M₂ → Fin B.size)
    (SelectedA : Fin M₁ → Prop)
    (SelectedB : Fin M₂ → Prop)
    (hCommon : SameInitialL A.L B.L cut)
    (hUpper : ∀ R,
      (selectedStagePoolPrescribedData A cut originalA SelectedA).PrescribedUpperLType R ↔
      (selectedStagePoolPrescribedData B cut originalB SelectedB).PrescribedUpperLType R) :
    (selectedStagePoolPrescribedData A cut originalA SelectedA).CorrectedB3 family ↔
    (selectedStagePoolPrescribedData B cut originalB SelectedB).CorrectedB3 family := by
  constructor
  · intro hA
    exact selectedStagePool_crossAmbient_B3_of_upperL
      family B A cut hCutB hCutA originalB originalA
      SelectedB SelectedA
      (crossAmbient_sameInitialL_reverse hCommon)
      (fun R hR => (hUpper R).2 hR) hA
  · intro hB
    exact selectedStagePool_crossAmbient_B3_of_upperL
      family A B cut hCutA hCutB originalA originalB
      SelectedA SelectedB hCommon
      (fun R hR => (hUpper R).1 hR) hB

#print axioms selectedStagePool_crossAmbient_socle_coverage_of_upperL
#print axioms selectedStagePool_crossAmbient_B3_of_upperL
#print axioms selectedStagePool_crossAmbient_B3_iff_equal_upperL

end Kk
