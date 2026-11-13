import Kk.B3ActualI3ExtraUpper
import Mathlib.Tactic

/-!
# Track B: complete upper ordinary-L profiles suffice for corrected B3

English proof and adversarial audit were committed FIRST:
  docs/track_b_upper_L_profile_sufficiency_english_audit.md

Every two genuinely selected, eligible original-name pools inside
ONE finite ambient structure have mutually matching OLD L socles when
both pools are nonempty. Thus the finite corrected-B3 age test is
determined by its complete permitted UPPER ordinary-L reduct family,
not by the extra E bits on the prescribed source records.

This is a positive CONDITIONAL transfer principle. The omitted
auxiliary q2 upper type in the actual K4 gadget shows why it does
not automatically apply to the selected macrodiary alone.
-/

namespace Kk

open SuccessorTree.V10

/-- One-sided exact sufficient criterion for passing the *FULL*
corrected B3 test of two genuine cut-eligible selected source pools.
It requires only inclusion of their complete allowed upper L types
in the right direction, since their old L socles match automatically. -/
theorem selectedStagePool_correctedB3_of_upperL_coverage
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Full Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hUpper : ∀ R,
      (selectedStagePoolPrescribedData A cut original Full).PrescribedUpperLType R →
      (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType R)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    (selectedStagePoolPrescribedData A cut original Full).CorrectedB3 family := by
  exact correctedB3_of_Lprofile_dominance
    (selectedStagePoolPrescribedData A cut original Full)
    (selectedStagePoolPrescribedData A cut original Marked)
    family
    (selectedStagePool_full_to_marked_Lsocle_coverage
      A cut hCut original Full Marked w hw hwCut)
    hUpper hMarked

/-- For two NONEMPTY actual selected original pools in the SAME
ambient A, equality of the complete permitted upper L-reduct
predicates is enough for equivalence of the whole corrected B3
tests, regardless of extra E records or original-name labels.

This says nothing about complete labelled L+ envelope equality. -/
theorem selectedStagePool_correctedB3_iff_equal_upperL_profiles
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Full Marked : Fin M → Prop)
    (wFull : Fin M) (hwFull : Full wFull)
    (hwFullCut : cut+1 ≤ A.freeLevel (original wFull).val)
    (wMarked : Fin M) (hwMarked : Marked wMarked)
    (hwMarkedCut : cut+1 ≤ A.freeLevel (original wMarked).val)
    (hUpper : ∀ R,
      (selectedStagePoolPrescribedData A cut original Full).PrescribedUpperLType R ↔
      (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType R) :
    (selectedStagePoolPrescribedData A cut original Full).CorrectedB3 family ↔
    (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family := by
  apply correctedB3_iff_of_equal_Lprofiles
    (selectedStagePoolPrescribedData A cut original Full)
    (selectedStagePoolPrescribedData A cut original Marked)
    family
  · exact selectedStagePool_full_to_marked_Lsocle_coverage
      A cut hCut original Full Marked wMarked hwMarked hwMarkedCut
  · intro R hR
    exact (hUpper R).1 hR
  · exact selectedStagePool_full_to_marked_Lsocle_coverage
      A cut hCut original Marked Full wFull hwFull hwFullCut
  · intro R hR
    exact (hUpper R).2 hR

/-- Apply the sufficient upper-L-profile test to the ACTUAL
chosen closure source of one Kpt finite stage, not to every
cut-eligible ambient original. Its selected predicate comes from
closure nodes that genuinely cross cut. -/
theorem closureSelectedBoringData_correctedB3_of_marked_upperL_coverage
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hUpper : ∀ R,
      (closureSelectedBoringData family A hAvoid original Z cut).PrescribedUpperLType R →
      (selectedStagePoolPrescribedData A cut original Marked).PrescribedUpperLType R)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    (closureSelectedBoringData family A hAvoid original Z cut).CorrectedB3
      family := by
  exact selectedStagePool_correctedB3_of_upperL_coverage
    family A cut hCut original
    (closureSelectedOriginal family A hAvoid original Z cut)
    Marked w hw hwCut hUpper hMarked

/-- A more concrete, ORIGINAL-NAME-based certificate for the
complete full-to-marked upper-L inclusion. It compares the
CHOSEN target of each full source type with the CHOSEN target
of an eligible marked old type, not with a potentially unrelated
next type of an arbitrary duplicate old-name representative. -/
theorem selectedStagePool_correctedB3_of_named_upper_target_cover
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (original : Fin M → Fin A.size)
    (Full Marked : Fin M → Prop)
    (w : Fin M) (hw : Marked w)
    (hwCut : cut+1 ≤ A.freeLevel (original w).val)
    (hNameCover : ∀ S,
      S ∈ (selectedStagePoolPrescribedData A cut original Full).source →
      ∃ v : Fin M, Marked v ∧ cut+1 ≤ A.freeLevel (original v).val ∧
        ((selectedStagePoolPrescribedData A cut original Full).target S).lReduct =
        ((selectedStagePoolPrescribedData A cut original Marked).target
          (A.partialTypeAt cut (original v).val)).lReduct)
    (hMarked :
      (selectedStagePoolPrescribedData A cut original Marked).CorrectedB3 family) :
    (selectedStagePoolPrescribedData A cut original Full).CorrectedB3 family := by
  classical
  let F : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut original Full
  let G : PrescribedBoringData cut db du dd :=
    selectedStagePoolPrescribedData A cut original Marked
  have hUpper : ∀ R, F.PrescribedUpperLType R →
      G.PrescribedUpperLType R := by
    intro R hR
    obtain ⟨S,hS,hUpperEq⟩ := hR
    obtain ⟨v,hMark,hFree,hSame⟩ := hNameCover S hS
    let T : PartialTypeWithE cut db du dd :=
      A.partialTypeAt cut (original v).val
    have hT : T ∈ G.source := by
      change ∃ u : Fin M,
        (Marked u ∧ cut+1 ≤ A.freeLevel (original u).val) ∧
          A.partialTypeAt cut (original u).val = T
      exact ⟨v,⟨hMark,hFree⟩,rfl⟩
    refine ⟨T,hT,?_⟩
    calc
      R = (F.target S).lReduct := hUpperEq
      _ = (G.target T).lReduct := hSame
  exact selectedStagePool_correctedB3_of_upperL_coverage
    family A cut hCut original Full Marked w hw hwCut hUpper hMarked

#print axioms selectedStagePool_correctedB3_of_upperL_coverage
#print axioms selectedStagePool_correctedB3_iff_equal_upperL_profiles
#print axioms closureSelectedBoringData_correctedB3_of_marked_upperL_coverage
#print axioms selectedStagePool_correctedB3_of_named_upper_target_cover

end Kk
