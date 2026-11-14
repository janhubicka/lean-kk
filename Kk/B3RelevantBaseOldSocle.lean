import Kk.B3FullSourceCertification
import SuccessorTree.V10.HNumericBinary
import SuccessorTree.V10.BlockOrder
import Mathlib.Tactic

/-!
# Track B: only FINITELY many REAL base pairs determine an old Henson L socle

English-first proof + seventeen hostile checks:
  docs/track_b_relevant_base_old_socle_english_audit.md

At a physical numerical-H source-coordinate cut c, the OLD ordinary-L
binary atoms are exactly copied from the base-graph pairs whose
admissible REAL generation coordinates BOTH lie at or before c.

Matching the two directed original-base atoms ONLY on this finite
set (and the base diagonal) suffices for complete old ordinary-L
socle agreement of two numerical-H structures over DIFFERENT E.

Unlike the old same-base lemma, the physical base graphs may differ
arbitrarily outside these finitely relevant pairs; same generation
k and literal source-coordinate cut remain hypotheses.

This is a conditional finite alignment criterion, NOT a proof that
the refined diary supplies base-pair alignment or source-rank transport.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A REAL base-original pair can contribute old ordinary-L atoms
at physical cut c iff some allowed generation pair of its copies
lies entirely in the old source prefix through c.

The actual numerical-H gate is q<m or the top-top q=m=k case.
Odd fake coordinates and nongated real pairs cannot contribute.
-/
def HensonRelevantBasePair (k cut i j : Nat) : Prop :=
  ∃ q m : Nat,
    i < j ∧ q ≤ k ∧ m ≤ k ∧
    (q < m ∨ (q = m ∧ m = k)) ∧
    hPosition k i q ≤ cut ∧ hPosition k j m ≤ cut

/-- The relevant base-original edge pairs are FINITELY localized:
both base indices are at most the source-coordinate cut itself.

This bound does not assert a diary-uniform source size: it is a
literal finite cut bound, using hPosition(k,j,m)≥j. -/
theorem relevant_base_pair_base_indices_bounded
    (k cut i j : Nat)
    (h : HensonRelevantBasePair k cut i j) :
    i < j ∧ j ≤ cut := by
  obtain ⟨q,m,hij,_hq,_hm,_hGate,_hPosI,hPosJ⟩ := h
  have hGeom : j ≤ hPosition k j m := by
    unfold hPosition
    have hCoeff : 1 ≤ 2*(k+1) := by omega
    have hMul : j ≤ (2*(k+1))*j := by
      simpa only [one_mul] using Nat.mul_le_mul_right j hCoeff
    omega
  exact ⟨hij, hGeom.trans hPosJ⟩

/-- Matching BOTH directed real base-graph bits on the genuinely
admissible OLD H generation pairs forces equality of EVERY complete
old directed H L-binary atom, including all absent bits.

No base graph symmetry, K_ell-freeness or auxiliary E equality is
required for this elementary copying lemma. These enter later
only for true Henson occurrence/forbidden-family certificates.
-/
theorem numericalH_old_binary_eq_of_relevant_base_pairs
    (E F : Nat → Nat → Bool)
    (k cut : Nat)
    (hBase : ∀ i j, HensonRelevantBasePair k cut i j →
      E i j = F i j ∧ E j i = F j i)
    (x y : Nat) (hx : x ≤ cut) (hy : y ≤ cut) :
    hNumericBinary (normalizedGraphModel E).binary
      k x y (0 : Fin 1) =
    hNumericBinary (normalizedGraphModel F).binary
      k x y (0 : Fin 1) := by
  classical
  have hTransfer :
      ∀ (G H : Nat → Nat → Bool),
        (∀ i j, HensonRelevantBasePair k cut i j →
          G i j = H i j ∧ G j i = H j i) →
        HNumericCrossing (normalizedGraphModel G).binary
          k x y (0 : Fin 1) →
        HNumericCrossing (normalizedGraphModel H).binary
          k x y (0 : Fin 1) := by
    intro G H hG hCross
    obtain ⟨i,j,q,m,hij,hq,hm,hgate,hDir⟩ := hCross
    have hRelevant : HensonRelevantBasePair k cut i j := by
      rcases hDir with ⟨hX,hY,_hBit⟩ | ⟨hX,hY,_hBit⟩
      · refine ⟨q,m,hij,hq,hm,hgate,?_,?_⟩
        · simpa only [hX] using hx
        · simpa only [hY] using hy
      · refine ⟨q,m,hij,hq,hm,hgate,?_,?_⟩
        · simpa only [hY] using hy
        · simpa only [hX] using hx
    obtain ⟨hForward,hBackward⟩ := hG i j hRelevant
    refine ⟨i,j,q,m,hij,hq,hm,hgate,?_⟩
    rcases hDir with ⟨hX,hY,hBit⟩ | ⟨hX,hY,hBit⟩
    · apply Or.inl
      refine ⟨hX,hY,?_⟩
      change G i j = true at hBit
      change H i j = true
      rw [← hForward]
      exact hBit
    · apply Or.inr
      refine ⟨hX,hY,?_⟩
      change G j i = true at hBit
      change H j i = true
      rw [← hBackward]
      exact hBit
  have hCross : HNumericCrossing
        (normalizedGraphModel E).binary
        k x y (0 : Fin 1) ↔
      HNumericCrossing (normalizedGraphModel F).binary
        k x y (0 : Fin 1) := by
    constructor
    · exact hTransfer E F hBase
    · exact hTransfer F E
        (fun i j hRel =>
          ⟨(hBase i j hRel).1.symm,(hBase i j hRel).2.symm⟩)
  have hTrue :
      (hNumericBinary (normalizedGraphModel E).binary
        k x y (0 : Fin 1) = true) ↔
      (hNumericBinary (normalizedGraphModel F).binary
        k x y (0 : Fin 1) = true) := by
    rw [hNumericBinary_true_iff, hNumericBinary_true_iff]
    exact hCross
  cases he : hNumericBinary (normalizedGraphModel E).binary
      k x y (0 : Fin 1) with
  | false =>
      cases hf : hNumericBinary (normalizedGraphModel F).binary
          k x y (0 : Fin 1) with
      | false => rfl
      | true =>
          have hWrong := hTrue.mpr hf
          rw [he] at hWrong
          contradiction
  | true =>
      have hf := hTrue.mp he
      rw [he,hf]

/-- Two DIFFERENT graph base models with the same numerical-H
generation k agree on their FULL old ordinary-L socle through c
if their finite real OLD gate pairs have equal directed base bits
and their base loop/diagonal bits agree.

All present/absent ordered binary, carrier, unary and diagonal L
atoms are preserved. This statement does NOT compare auxiliary E
or physical Kpt source crossing records. -/
theorem numericalH_old_socle_eq_of_relevant_base_pairs
    (E F : Nat → Nat → Bool)
    (k N₁ N₂ cut : Nat)
    (hCut₁ : cut < N₁) (hCut₂ : cut < N₂)
    (hBase : ∀ i j, HensonRelevantBasePair k cut i j →
      E i j = F i j ∧ E j i = F j i)
    (hDiag : ∀ i : Nat, E i i = F i i) :
    SameInitialL
      (finiteNumericHL (normalizedGraphModel E) k N₁)
      (finiteNumericHL (normalizedGraphModel F) k N₂)
      cut := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    change (x < N₁) ↔ (x < N₂)
    omega
  · intro x y hx hy t
    have ht : t = (0 : Fin 1) := Subsingleton.elim _ _
    subst t
    change hNumericBinary (normalizedGraphModel E).binary
      k x y (0 : Fin 1) =
      hNumericBinary (normalizedGraphModel F).binary
      k x y (0 : Fin 1)
    exact numericalH_old_binary_eq_of_relevant_base_pairs
      E F k cut hBase x y hx hy
  · intro x hx t
    exact Fin.elim0 t
  · intro x hx t
    change hNumericSingleton (normalizedGraphModel E).diagonal k x t =
      hNumericSingleton (normalizedGraphModel F).diagonal k x t
    have hSameDiagonal :
        (normalizedGraphModel E).diagonal =
        (normalizedGraphModel F).diagonal := by
      funext i a
      change E i i = F i i
      exact hDiag i
    rw [hSameDiagonal]

namespace HensonCutOccurrence

variable {ell cut : Nat} {hell : 2 ≤ ell}

/-- Two true finite physical Henson source occurrences may use
DIFFERENT base graphs, as long as their numerical-H generation k
agrees and the two directed base edge values agree on the finite
set of real generation pairs that can occur at or below cut.

Both base diagonals are false by the explicit Henson loop-free
certificates, so the complete ordinary-L old socle follows. -/
theorem old_socle_of_relevant_base_pair_agreement
    (P Q : HensonCutOccurrence ell cut hell)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i) :
    SameInitialL P.ambient.L Q.ambient.L cut := by
  change SameInitialL
    (finiteNumericHL (normalizedGraphModel P.E) P.k P.N)
    (finiteNumericHL (normalizedGraphModel Q.E) Q.k Q.N)
    cut
  rw [← hk]
  exact numericalH_old_socle_eq_of_relevant_base_pairs
    P.E Q.E P.k P.N Q.N cut P.hCut Q.hCut hBase
    (fun i => (P.hLoops i).trans (Q.hLoops i).symm)

/-- For two EXHAUSTIVE physical Henson occurrences at a shared cut,
the old-L-socle alignment hypothesis of cross-occurrence full
corrected B3 transfer can be discharged by matching ONLY finitely
many relevant directed base edge pairs, not entire base graphs.

Equality of intrinsic positive-cut complete UPPER ordinary-L
spectra remains a separate, genuine input. Exact Full names and
pool exhaustiveness remain explicit certificates for each
physical occurrence (derived for actual runs in Track B #154). -/
theorem full_B3_iff_of_relevant_base_and_intrinsic_cutStar
    (P Q : HensonCutOccurrence ell cut hell)
    (hk : P.k = Q.k)
    (hBase : ∀ i j,
      HensonRelevantBasePair P.k cut i j →
      P.E i j = Q.E i j ∧ P.E j i = Q.E j i)
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
    (old_socle_of_relevant_base_pair_agreement
      P Q hk hBase) hPhysical

end HensonCutOccurrence

#print axioms Kk.relevant_base_pair_base_indices_bounded
#print axioms Kk.numericalH_old_binary_eq_of_relevant_base_pairs
#print axioms Kk.numericalH_old_socle_eq_of_relevant_base_pairs
#print axioms Kk.HensonCutOccurrence.old_socle_of_relevant_base_pair_agreement
#print axioms Kk.HensonCutOccurrence.full_B3_iff_of_relevant_base_and_intrinsic_cutStar

end Kk
