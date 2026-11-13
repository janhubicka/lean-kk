import Kk.B3ProfileGapAudit
import SuccessorTree.V10.I3AmbientSocleBridge

/-!
# Track B: a common actual ambient L-socle eliminates one B3 gap

English-first mathematical proof + hostile audit:
  docs/track_b_ambient_pool_socle_english_audit.md

Two source/target functions constructed from NONEMPTY marked and
arbitrary full finite pools of original names in the SAME enumerated
partial structure share the old ordinary-L socle at every tested cut.

Consequently a failing full corrected B3 test alongside a passing
marked test forces a MISSING complete upper L-reduct.

The actual AlgorithmRun parameter-closed source is not asserted to be
an ambientPoolPrescribedData: establishing that representation remains
the separate geometric obligation for the resolved diary.
-/

namespace Kk

open SuccessorTree.V10

/-- For two actual finite original-name pools in a COMMON ambient
partial structure, every full old source has a marked representative
with the same complete old ordinary-L socle, provided the marked
pool contains at least one actual name and cut < A.size.

No injectivity, forbidden-free condition, E comparison, or equality
of the upper type vertices is assumed. -/
theorem ambientPool_full_to_marked_Lsocle_coverage
    {db du dd M N : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (fullOriginal : Fin M → Nat)
    (markedOriginal : Fin N → Nat)
    (w : Fin N) :
    ∀ S, S ∈ (ambientPoolPrescribedData A cut fullOriginal).source →
      ∃ T, T ∈ (ambientPoolPrescribedData A cut markedOriginal).source ∧
        SameInitialL
          (prescribedOrdinarySocle
            ((ambientPoolPrescribedData A cut fullOriginal).target S))
          (prescribedOrdinarySocle
            ((ambientPoolPrescribedData A cut markedOriginal).target T)) cut := by
  classical
  intro S hS
  obtain ⟨v,hFullTarget⟩ :=
    ambientPoolPrescribedData_target_original A cut fullOriginal S hS
  let T : PartialTypeWithE cut db du dd :=
    A.partialTypeAt cut (markedOriginal w)
  have hT : T ∈ (ambientPoolPrescribedData A cut markedOriginal).source := by
    change ∃ z : Fin N, A.partialTypeAt cut (markedOriginal z) = T
    exact ⟨w,rfl⟩
  obtain ⟨u,hMarkedTarget⟩ :=
    ambientPoolPrescribedData_target_original A cut markedOriginal T hT
  refine ⟨T,hT,?_⟩
  rw [hFullTarget,hMarkedTarget]
  have hMarked : SameInitialL
      (prescribedOrdinarySocle
        (A.partialTypeAt (cut+1) (markedOriginal u))) A.L cut :=
    ambient_partialType_prescribedSocle A cut (markedOriginal u) hCut
  have hReverse : SameInitialL A.L
      (prescribedOrdinarySocle
        (A.partialTypeAt (cut+1) (markedOriginal u))) cut := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      exact (hMarked.1 x hx).symm
    · intro x y hx hy t
      exact (hMarked.2.1 x y hx hy t).symm
    · intro x hx t
      exact (hMarked.2.2.1 x hx t).symm
    · intro x hx t
      exact (hMarked.2.2.2 x hx t).symm
  exact (ambient_partialType_prescribedSocle
    A cut (fullOriginal v) hCut).trans hReverse

/-- Whenever the ACTUAL full and marked B3 profiles both come
from original-name pools in one fixed ambient partial structure,
and the marked pool is nonempty, a passing marked test and failing
full test REQUIRE an additional complete upper ordinary-L reduct.

This discharges old-L-socle coverage for these finite actual pools,
but it does NOT identify the parameter-closed AlgorithmRun source
with one of the pools. -/
theorem ambientPool_fullB3_failure_requires_extra_upperL
    {db du dd M N : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (cut : Nat) (hCut : cut < A.size)
    (fullOriginal : Fin M → Nat)
    (markedOriginal : Fin N → Nat)
    (w : Fin N)
    (family : List (NormalizedForbidden db du dd))
    (hFailure :
      ¬ (ambientPoolPrescribedData A cut fullOriginal).CorrectedB3 family)
    (hMarked :
      (ambientPoolPrescribedData A cut markedOriginal).CorrectedB3 family) :
    ∃ R,
      (ambientPoolPrescribedData A cut fullOriginal).PrescribedUpperLType R ∧
      ¬ (ambientPoolPrescribedData A cut markedOriginal).PrescribedUpperLType R := by
  exact fullB3_failure_good_marked_missing_upper
    (ambientPoolPrescribedData A cut fullOriginal)
    (ambientPoolPrescribedData A cut markedOriginal)
    family
    (ambientPool_full_to_marked_Lsocle_coverage
      A cut hCut fullOriginal markedOriginal w)
    hFailure hMarked

#print axioms ambientPool_full_to_marked_Lsocle_coverage
#print axioms ambientPool_fullB3_failure_requires_extra_upperL

end Kk
