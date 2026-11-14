import Kk.B3TwoRunsRelevantBaseTransfer
import SuccessorTree.V10.HNumericBinary
import Mathlib.Tactic

/-!
# Track B: an EXACT finite fingerprint for OLD Henson ordinary-L socles

English proof and thirteen hostile checks were committed FIRST:
  docs/track_b_relevant_base_exact_fingerprint_english_audit.md

For two finite physical symmetric loop-free Henson occurrences
with the SAME numerical generation k and SOURCE coordinate cut c,
equality of their COMPLETE OLD ordinary-L socles is EQUIVALENT
to equality of both directed base-original edge bits on the finite
`HensonRelevantBasePair k c` set.

The prior checked base-support theorem proved sufficiency.
The new reverse implication uses the actual physical copies at
admissible generations q,m≤k, and the successor library's
hNumericBinary_real_forward_iff to recover each base edge
from an OLD numerical-H directed binary atom. Physical symmetry
then recovers the reverse directed atom.

This local finite fingerprint is not a proof that the diary aligns
physical source cuts, preserves auxiliary Kpt E/parameter records,
or canonically matches positive-cut UPPER source profiles.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

namespace HensonCutOccurrence

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- EXACT finite old ordinary-L prefix certificate:
two physical finite Henson occurrences with equal numerical
generation k have the same complete old ordinary-L socle
through the common cut c IFF their ORIGINAL base graph atoms
agree in BOTH directions on every admissible real copy pair
whose physical numerical-H coordinates lie at/below c.

The reverse implication is the checked source-support theorem.
The forward direction reconstructs the real base edge from
the complete OLD physical binary atom, using the precisely
gated real-copy Boolean semantics and loop-free symmetry.

No base graph equality outside the finite relevant set,
E auxiliary source equality, upper B3 profile matching
or same-diary orbit assertion is hidden in this theorem. -/
theorem old_socle_iff_relevant_base_pair_agreement
    (P Q : HensonCutOccurrence ell cut hell)
    (hk : P.k = Q.k) :
    SameInitialL P.ambient.L Q.ambient.L cut ↔
      ∀ i j,
        HensonRelevantBasePair P.k cut i j →
        P.E i j = Q.E i j ∧ P.E j i = Q.E j i := by
  constructor
  · intro hOld i j hRelevant
    obtain ⟨q,m,hij,hq,hm,hGate,hPosI,hPosJ⟩ := hRelevant
    have hOldPhysical : SameInitialL
        (finiteNumericHL (normalizedGraphModel P.E) P.k P.N)
        (finiteNumericHL (normalizedGraphModel Q.E) P.k Q.N) cut := by
      change SameInitialL
        (finiteNumericHL (normalizedGraphModel P.E) P.k P.N)
        (finiteNumericHL (normalizedGraphModel Q.E) Q.k Q.N)
        cut at hOld
      rw [← hk] at hOld
      exact hOld
    have hPhysicalEq :
        hNumericBinary (normalizedGraphModel P.E).binary P.k
          (hPosition P.k i q) (hPosition P.k j m) (0 : Fin 1) =
        hNumericBinary (normalizedGraphModel Q.E).binary P.k
          (hPosition P.k i q) (hPosition P.k j m) (0 : Fin 1) := by
      exact hOldPhysical.2.1
        (hPosition P.k i q) (hPosition P.k j m)
        hPosI hPosJ (0 : Fin 1)
    have hBitIff : (P.E i j = true) ↔ (Q.E i j = true) := by
      constructor
      · intro hPositiveP
        have hNumP :
            hNumericBinary (normalizedGraphModel P.E).binary P.k
              (hPosition P.k i q) (hPosition P.k j m)
              (0 : Fin 1) = true :=
          (hNumericBinary_real_forward_iff
            (normalizedGraphModel P.E).binary P.k i j q m
            (0 : Fin 1) hij hq hm).2
            ⟨hGate,hPositiveP⟩
        have hNumQ :
            hNumericBinary (normalizedGraphModel Q.E).binary P.k
              (hPosition P.k i q) (hPosition P.k j m)
              (0 : Fin 1) = true := by
          rw [← hPhysicalEq]
          exact hNumP
        exact ((hNumericBinary_real_forward_iff
          (normalizedGraphModel Q.E).binary P.k i j q m
          (0 : Fin 1) hij hq hm).1 hNumQ).2
      · intro hPositiveQ
        have hNumQ :
            hNumericBinary (normalizedGraphModel Q.E).binary P.k
              (hPosition P.k i q) (hPosition P.k j m)
              (0 : Fin 1) = true :=
          (hNumericBinary_real_forward_iff
            (normalizedGraphModel Q.E).binary P.k i j q m
            (0 : Fin 1) hij hq hm).2
            ⟨hGate,hPositiveQ⟩
        have hNumP :
            hNumericBinary (normalizedGraphModel P.E).binary P.k
              (hPosition P.k i q) (hPosition P.k j m)
              (0 : Fin 1) = true := by
          rw [hPhysicalEq]
          exact hNumQ
        exact ((hNumericBinary_real_forward_iff
          (normalizedGraphModel P.E).binary P.k i j q m
          (0 : Fin 1) hij hq hm).1 hNumP).2
    have hForward : P.E i j = Q.E i j := by
      cases hp : P.E i j with
      | false =>
          cases hq : Q.E i j with
          | false => rfl
          | true =>
              have hContr := hBitIff.mpr hq
              rw [hp] at hContr
              contradiction
      | true =>
          have hQ := hBitIff.mp hp
          exact hQ.symm
    have hReverse : P.E j i = Q.E j i := by
      calc
        P.E j i = P.E i j := P.hSym j i
        _ = Q.E i j := hForward
        _ = Q.E j i := (Q.hSym j i).symm
    exact ⟨hForward,hReverse⟩
  · intro hBase
    exact old_socle_of_relevant_base_pair_agreement
      P Q hk hBase

end HensonCutOccurrence

namespace HensonPhysicalRunCutData

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- For two TRUE finite Henson AlgorithmRuns over possibly
different base graphs E, the FINITE relevant original-base
edge table is a NECESSARY-AND-SUFFICIENT certificate for
equality of complete OLD ordinary-L source prefixes, provided
their numerical generation k and literal source cut c agree.

All actual source/fullness and no-I2 certificates are fields of
the two runs; this theorem does not assert their positive-cut
UPPER-L spectra agree, or that a refined diary determines it. -/
theorem old_socle_iff_finite_base_pair_fingerprint
    (P Q : HensonPhysicalRunCutData ell hell cut)
    (hk : P.k = Q.k) :
    SameInitialL P.occurrence.ambient.L Q.occurrence.ambient.L cut ↔
      ∀ i j,
        HensonRelevantBasePair P.k cut i j →
        P.E i j = Q.E i j ∧ P.E j i = Q.E j i := by
  exact HensonCutOccurrence.old_socle_iff_relevant_base_pair_agreement
    P.occurrence Q.occurrence hk

end HensonPhysicalRunCutData

#print axioms Kk.HensonCutOccurrence.old_socle_iff_relevant_base_pair_agreement
#print axioms Kk.HensonPhysicalRunCutData.old_socle_iff_finite_base_pair_fingerprint

end Kk
