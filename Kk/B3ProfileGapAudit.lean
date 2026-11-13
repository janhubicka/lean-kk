import Kk.B3ReductProfile

/-!
# Track B: necessary profile defects for full corrected-(B3) failure

English-first argument and adversarial audit:
  docs/track_b_full_b3_profile_gap_english_audit.md

The existing transfer theorem says that full-source ordinary-L socle
coverage plus inclusion of complete full upper L-reducts in the marked
profile transfers passing corrected B3 from marked to full.

This module extracts the exact contrapositive. If marked passes but
full fails, one of those TWO finite profile conditions necessarily
fails. It never asserts that a resolved numerical-H diary satisfies
either condition, or that B3 profiles determine a labelled orbit.
-/

namespace Kk

open SuccessorTree.V10

/-- If the full parameter-closed B3 test fails but a marked test passes,
there is either a full source without a corresponding marked old
ordinary-L socle, OR a full permitted complete upper L-reduct absent
from the marked upper-type family.

This is a diagnostic disjunction, not a global diary projection. -/
theorem fullB3_failure_good_marked_profile_gap
    {cut db du dd : Nat}
    (full marked : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hFailure : ¬ full.CorrectedB3 family)
    (hMarked : marked.CorrectedB3 family) :
    (∃ S, S ∈ full.source ∧
      ∀ T, T ∈ marked.source →
        ¬ SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut) ∨
    (∃ R, full.PrescribedUpperLType R ∧
      ¬ marked.PrescribedUpperLType R) := by
  classical
  by_contra hNoGap
  have hSocle : ∀ S, S ∈ full.source →
      ∃ T, T ∈ marked.source ∧
        SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut := by
    intro S hS
    by_contra hNoMatch
    apply hNoGap
    refine Or.inl ⟨S, hS, ?_⟩
    intro T hT hSame
    exact hNoMatch ⟨T, hT, hSame⟩
  have hUpper : ∀ R, full.PrescribedUpperLType R →
      marked.PrescribedUpperLType R := by
    intro R hFull
    by_contra hMissing
    exact hNoGap (Or.inr ⟨R, hFull, hMissing⟩)
  exact hFailure
    (correctedB3_of_Lprofile_dominance
      full marked family hSocle hUpper hMarked)

/-- When every full old ordinary-L socle is represented by a marked
source, any failed full B3 test with a passing marked test forces a
specific MISSING complete upper L-reduct. This is the important K4
auxiliary-type obstruction in abstract form. -/
theorem fullB3_failure_good_marked_missing_upper
    {cut db du dd : Nat}
    (full marked : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hSocle : ∀ S, S ∈ full.source →
      ∃ T, T ∈ marked.source ∧
        SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut)
    (hFailure : ¬ full.CorrectedB3 family)
    (hMarked : marked.CorrectedB3 family) :
    ∃ R, full.PrescribedUpperLType R ∧
      ¬ marked.PrescribedUpperLType R := by
  classical
  by_contra hNoMissing
  have hUpper : ∀ R, full.PrescribedUpperLType R →
      marked.PrescribedUpperLType R := by
    intro R hFull
    by_contra hMissing
    exact hNoMissing ⟨R, hFull, hMissing⟩
  exact hFailure
    (correctedB3_of_Lprofile_dominance
      full marked family hSocle hUpper hMarked)

/-- Dually, if the complete upper L-type inclusion does hold, a
passing marked test and failing full test force a full original source
which has no marked representative with the same ordinary-L socle. -/
theorem fullB3_failure_good_marked_missing_socle
    {cut db du dd : Nat}
    (full marked : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hUpper : ∀ R, full.PrescribedUpperLType R →
      marked.PrescribedUpperLType R)
    (hFailure : ¬ full.CorrectedB3 family)
    (hMarked : marked.CorrectedB3 family) :
    ∃ S, S ∈ full.source ∧
      ∀ T, T ∈ marked.source →
        ¬ SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut := by
  classical
  by_contra hNoMissing
  have hSocle : ∀ S, S ∈ full.source →
      ∃ T, T ∈ marked.source ∧
        SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut := by
    intro S hS
    by_contra hNoMatch
    apply hNoMissing
    refine ⟨S, hS, ?_⟩
    intro T hT hSame
    exact hNoMatch ⟨T, hT, hSame⟩
  exact hFailure
    (correctedB3_of_Lprofile_dominance
      full marked family hSocle hUpper hMarked)

#print axioms fullB3_failure_good_marked_profile_gap
#print axioms fullB3_failure_good_marked_missing_upper
#print axioms fullB3_failure_good_marked_missing_socle

end Kk
