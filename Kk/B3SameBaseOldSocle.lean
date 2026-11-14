import Kk.B3FullSourceCertification
import Mathlib.Tactic

/-!
# Track B: SAME BASE numerical H has SAME old ordinary-L prefixes

English proof and fifteen adversarial checks committed first:
  docs/track_b_same_base_old_L_socle_english_audit.md

For finite numerical-H truncations at heights N₁,N₂ built
from ONE base AgeTestModel K and ONE generation parameter k,
all ordinary-L relation functions are literally identical.
Only carrier truncation depends on N. Thus their complete
old ordinary-L prefixes coincide at any cut present in BOTH.

The physical HensonCutOccurrence specialization discharges the
old-socle alignment assumption when two occurrences use the SAME
original E and k, despite different actual original-name pools,
parameter-closed sources and truncation sizes.

This does NOT prove their cut-star upper-type spectra agree
or provide any full labelled orbit/BRD theorem.
-/

namespace Kk

open SuccessorTree.V10

/-- Every two finite numerical-H L-reducts built from the SAME
age model K and generation parameter k have exactly the same
complete old ordinary-L socle through any cut in BOTH carriers.

All directed binary, unary, diagonal and ABSENT atoms are equal;
the finite parameter N only truncates the carrier. -/
theorem finiteNumericHL_same_base_old_socle
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N₁ N₂ cut : Nat)
    (hCut₁ : cut < N₁) (hCut₂ : cut < N₂) :
    SameInitialL
      (finiteNumericHL K k N₁)
      (finiteNumericHL K k N₂)
      cut := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    change (x < N₁) ↔ (x < N₂)
    omega
  · intro x y hx hy t
    change hNumericBinary K.binary k x y t =
      hNumericBinary K.binary k x y t
    rfl
  · intro x hx t
    change hNumericSingleton K.unary k x t =
      hNumericSingleton K.unary k x t
    rfl
  · intro x hx t
    change hNumericSingleton K.diagonal k x t =
      hNumericSingleton K.diagonal k x t
    rfl

namespace HensonCutOccurrence

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- Different physical Henson occurrences built over the SAME
base graph E and numerical generation parameter k have a
common old ordinary-L socle, even if N, named originals,
Full-selected source sets and actual Kpt closures differ.

The shared source cut is present in BOTH finite carriers by
the occurrence structure's explicit hCut fields. -/
theorem same_base_old_socle
    (P Q : HensonCutOccurrence ell cut hell)
    (hE : P.E = Q.E) (hk : P.k = Q.k) :
    SameInitialL P.ambient.L Q.ambient.L cut := by
  change SameInitialL
    (finiteNumericHL (normalizedGraphModel P.E) P.k P.N)
    (finiteNumericHL (normalizedGraphModel Q.E) Q.k Q.N)
    cut
  rw [← hE, ← hk]
  exact finiteNumericHL_same_base_old_socle
    (normalizedGraphModel P.E) P.k P.N Q.N
    cut P.hCut Q.hCut

/-- For two exhaustive physical occurrences over the SAME
base graph E and generation parameter k, equality of their
INTRINSIC positive-cut upper-L spectra alone suffices for
equivalence of their FULL corrected-B3 verdicts.

Exact Full-name and original-prefix exhaustion remain visible
premises for each occurrence. They follow separately from the
genuine AlgorithmRun construction under its seed pool hypotheses,
not merely from same-base old-prefix agreement. -/
theorem full_B3_iff_same_base_intrinsic_cutStar
    (P Q : HensonCutOccurrence ell cut hell)
    (hE : P.E = Q.E) (hk : P.k = Q.k)
    (hFullP : ∀ v : Fin P.M,
      P.Full v ↔ closureSelectedOriginal (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut v)
    (hPoolP : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) P.hAvoid (P.original v))
    (hFullQ : ∀ v : Fin Q.M,
      Q.Full v ↔ closureSelectedOriginal (hensonForbiddenFamily ell hell)
        Q.ambient Q.hAvoid Q.original Q.Z cut v)
    (hPoolQ : ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ Q.Z →
        ∃ v : Fin Q.M,
          z ≤ Q.ambient.kptOriginal
            (hensonForbiddenFamily ell hell) Q.hAvoid (Q.original v))
    (hPhysical : ∀ R : RelationalPrefixType (cut+1) 1 0 1,
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell) P.Z cut R ↔
      PhysicalCutStarUpperL (hensonForbiddenFamily ell hell) Q.Z cut R) :
    P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) ↔
    Q.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
  exact full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar
    P Q hFullP hPoolP hFullQ hPoolQ
    (same_base_old_socle P Q hE hk) hPhysical

end HensonCutOccurrence

#print axioms finiteNumericHL_same_base_old_socle
#print axioms HensonCutOccurrence.same_base_old_socle
#print axioms HensonCutOccurrence.full_B3_iff_same_base_intrinsic_cutStar

end Kk
