import Kk.B3CrossAmbientCutStar
import Kk.B3ClosureFibreCoherence
import Mathlib.Tactic

/-!
# Track B: compare physical cut-star ORIGINAL NAMES across occurrences

English-first proof and hostile audit:
  docs/track_b_cutstar_name_transport_english_audit.md

The previous cross-ambient B3 theorem used equality of complete
permitted upper ordinary-L reduct PREDICATES. This module proves
an application-facing criterion in terms of actual physical
cut-star ORIGINAL names and their complete next-cut L columns.

No-(I2) is essential: deduplicated chosen source targets agree
with ALL represented names of the same complete old L+ type
only when the genuine full closure has no competing meet at cut.
The conclusions are local B3 comparisons, not common source orbits.
-/

namespace Kk
namespace HensonCutOccurrence

open SuccessorTree
open SuccessorTree.V10

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- Every genuine selected physical cut-star original supplies its
OWN complete next-cut ordinary-L reduct as an actual permitted upper
type of the chosen source profile. This depends on real represented
closure membership and no-I2 full next-L+ fibre coherence.

In particular, merely having a name in an all-eligible ambient
pool would not suffice. -/
theorem star_name_complete_upperL_permitted
    (P : HensonCutOccurrence ell cut hell)
    (w : Fin P.M) (hw : P.starNames w) :
    P.starProfile.PrescribedUpperLType
      ((P.ambient.partialTypeAt (cut+1) (P.original w).val).lReduct) := by
  classical
  have hMarkedRepresented : ∀ v : Fin P.M, P.starNames v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut v := by
    intro v hv
    exact P.hRepresented v hv.1
  obtain ⟨z,_hz,hCross,hBelow⟩ :=
    hMarkedRepresented w hw
  have hFree : cut+1 ≤ P.ambient.freeLevel (P.original w).val := by
    have hLev := kptBelowOriginal_level_le_free
      (hensonForbiddenFamily ell hell) P.ambient P.hAvoid
      (P.original w) z hBelow
    omega
  let T : PartialTypeWithE cut 1 0 1 :=
    P.ambient.partialTypeAt cut (P.original w).val
  have hT : T ∈ P.starProfile.source := by
    change ∃ v : Fin P.M,
      (P.starNames v ∧ cut+1 ≤ P.ambient.freeLevel (P.original v).val) ∧
      P.ambient.partialTypeAt cut (P.original v).val = T
    exact ⟨w,⟨hw,hFree⟩,rfl⟩
  obtain ⟨u,hStarU,_hFreeU,hOldU,hNextU⟩ :=
    selectedStagePoolPrescribedData_source_original
      P.ambient cut P.original P.starNames T hT
  have hOldEq : P.ambient.partialTypeAt cut (P.original u).val =
      P.ambient.partialTypeAt cut (P.original w).val := by
    change P.ambient.partialTypeAt cut (P.original w).val =
      P.ambient.partialTypeAt cut (P.original u).val at hOldU
    exact hOldU.symm
  have hNextEq :
      P.ambient.partialTypeAt (cut+1) (P.original u).val =
      P.ambient.partialTypeAt (cut+1) (P.original w).val :=
    kpt_marked_next_full_type_eq_of_no_meet
      (hensonForbiddenFamily ell hell) P.ambient P.hAvoid
      P.original P.Z cut P.starNames
      hMarkedRepresented P.hNoI2
      u w hStarU hw hOldEq
  refine ⟨T,hT,?_⟩
  calc
    (P.ambient.partialTypeAt (cut+1) (P.original w).val).lReduct =
        (P.ambient.partialTypeAt (cut+1) (P.original u).val).lReduct :=
      congrArg
        (fun Q : PartialTypeWithE (cut+1) 1 0 1 => Q.lReduct)
        hNextEq.symm
    _ = (P.starProfile.target T).lReduct :=
      congrArg
        (fun Q : PartialTypeWithE (cut+1) 1 0 1 => Q.lReduct)
        hNextU.symm

/-- A physical name-by-name matching relation from P cut-star to
Q cut-star gives the complete inclusion of their chosen upper-L
PROFILE predicates. No injection/surjection of name indices is
assumed and distinct ambients may have different sizes and E data.

The target chosen-source representative is handled using
star_name_complete_upperL_permitted and its no-I2 hypothesis. -/
theorem star_upperL_inclusion_of_physical_name_cover
    (P Q : HensonCutOccurrence ell cut hell)
    (hNames : ∀ v : Fin P.M, P.starNames v →
      ∃ w : Fin Q.M, Q.starNames w ∧
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct =
        (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct) :
    ∀ R, P.starProfile.PrescribedUpperLType R →
      Q.starProfile.PrescribedUpperLType R := by
  classical
  intro R hR
  obtain ⟨S,hS,hReduct⟩ := hR
  obtain ⟨v,hStar,_hFree,_hOld,hNext⟩ :=
    selectedStagePoolPrescribedData_source_original
      P.ambient cut P.original P.starNames S hS
  obtain ⟨w,hStarQ,hEq⟩ := hNames v hStar
  have hType : R =
      (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct := by
    calc
      R = (P.starProfile.target S).lReduct := hReduct
      _ = (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct :=
        congrArg
          (fun T : PartialTypeWithE (cut+1) 1 0 1 => T.lReduct)
          hNext
      _ = (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct :=
        hEq
  rw [hType]
  exact star_name_complete_upperL_permitted Q w hStarQ

/-- At two independent finite Henson occurrences on the same
source cut, actual PHYSICAL cut-star original names can be matched
in both directions by their complete next-cut ordinary-L types.
Along with a common old ordinary-L socle this suffices for
equivalence of the FULL corrected-B3 tests.

The physical name-cover relations need not be injections or preserve
auxiliary E; no labelled monoid orbit is claimed. -/
theorem full_B3_crossAmbient_iff_of_physical_cutStar_name_cover
    (P Q : HensonCutOccurrence ell cut hell)
    (hOld : SameInitialL P.ambient.L Q.ambient.L cut)
    (hNamesPQ : ∀ v : Fin P.M, P.starNames v →
      ∃ w : Fin Q.M, Q.starNames w ∧
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct =
        (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct)
    (hNamesQP : ∀ w : Fin Q.M, Q.starNames w →
      ∃ v : Fin P.M, P.starNames v ∧
        (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct =
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct) :
    P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  apply full_B3_crossAmbient_iff_of_cutStar_profiles P Q hOld
  intro R
  constructor
  · exact star_upperL_inclusion_of_physical_name_cover P Q hNamesPQ R
  · exact star_upperL_inclusion_of_physical_name_cover Q P hNamesQP R

/-- A discrepancy between two full corrected-(B3) tests in
independent finite Henson occurrences forces an UNMATCHABLE
real, physically cut-adjacent name in the FAILING occurrence.

It has no counterpart with an identical COMPLETE next-cut L reduct
in the passing occurrence's own true cut-star, even if there are
multiple duplicate old-type labels. -/
theorem failing_full_B3_has_unmatchable_physical_cutStar_name
    (P Q : HensonCutOccurrence ell cut hell)
    (hOld : SameInitialL P.ambient.L Q.ambient.L cut)
    (hFailed : ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell))
    (hPassed : Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin P.M, P.starNames v ∧
      ∀ w : Fin Q.M, Q.starNames w →
        (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct ≠
        (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct := by
  classical
  obtain ⟨v,hFull,hEdge,_hFree,hMissing⟩ :=
    failing_full_B3_has_unmatched_cutStar_original P Q hOld hFailed hPassed
  have hStar : P.starNames v := ⟨hFull,hEdge⟩
  refine ⟨v,hStar,?_⟩
  intro w hw hEq
  have hAllowed := star_name_complete_upperL_permitted Q w hw
  rw [← hEq] at hAllowed
  exact hMissing hAllowed

end HensonCutOccurrence
end Kk

#print axioms Kk.HensonCutOccurrence.star_name_complete_upperL_permitted
#print axioms Kk.HensonCutOccurrence.star_upperL_inclusion_of_physical_name_cover
#print axioms Kk.HensonCutOccurrence.full_B3_crossAmbient_iff_of_physical_cutStar_name_cover
#print axioms Kk.HensonCutOccurrence.failing_full_B3_has_unmatchable_physical_cutStar_name
