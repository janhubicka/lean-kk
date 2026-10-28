import Kk.HensonI3CliqueWitness
import SuccessorTree.V10.RelationalTypeReduct
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The complete directed L-crossing prevents new asymmetry witnesses

The numerical-H corrected B3 witness is a finite L-only continuation
W with the same initial socle as an ambient L-structure C, and every
upper W vertex has the COMPLETE directed initial L-type of a named
ambient original. When C is symmetric across the tested cut, the
two directed edges between the cut and any upper W vertex agree.

If W without the tested cut avoids an asymmetric ordered pair, no
such pair can suddenly appear in W: a forbidden pair would have to
contain the cut, and all cut-crossing pairs are symmetric.

This is the missing zero-generation LOCAL implication. A
separate application must establish ambient cut-symmetry in the
actual numerical H model and obtain the complete named-original
types from the genuine selected-stage corrected B3 witness.

No assumption is made that arbitrary W is a symmetric graph;
its symmetry at exactly the relevant crossing is proved.
-/

namespace Kk

open SuccessorTree.V10

/-- For a two-vertex ordered continuation intersecting the tested
coordinate, complete directed upper-type equality and an ambient
symmetric crossing force the two directions to agree in W. -/
theorem two_point_B3_cross_symmetric
    (C W : AgeTestModel 1 0 1)
    (cut : Nat)
    (hSocle : SameInitialL W C cut)
    (hCrossSym : ∀ x : Nat,
      C.binary cut x (0 : Fin 1) = C.binary x cut (0 : Fin 1))
    (hUpper : ∀ x, x ∈ W.carrier → cut < x →
      ∃ original : Nat,
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) original)
    (e : Fin 2 → Nat)
    (hStrict : StrictMono e)
    (hCarrier : ∀ a, e a ∈ W.carrier)
    (hCut : e 0 = cut ∨ e 1 = cut) :
    W.binary (e 0) (e 1) (0 : Fin 1) =
      W.binary (e 1) (e 0) (0 : Fin 1) := by
  rcases hCut with h0 | h1
  · have hAbove : cut < e 1 := by
      have h := hStrict (show (0 : Fin 2) < 1 by decide)
      omega
    obtain ⟨v,hType⟩ := hUpper (e 1) (hCarrier 1) hAbove
    have hAtom := equal_reduct_types_imply_fullAtomic
      W C (cut+1) (e 1) v hType
    obtain ⟨hForward,hBackward⟩ :=
      fullAtomicTypePrefix_cross
        W.binary C.binary W.unary C.unary
        W.diagonal C.diagonal
        (cut+1) cut (e 1) v (Nat.lt_succ_self cut)
        hAtom (0 : Fin 1)
    rw [h0]
    exact hForward.trans ((hCrossSym v).trans hBackward.symm)
  · have hBelow : e 0 < cut := by
      have h := hStrict (show (0 : Fin 2) < 1 by decide)
      omega
    have hForward :=
      hSocle.2.1 (e 0) cut (Nat.le_of_lt hBelow)
        le_rfl (0 : Fin 1)
    have hBackward :=
      hSocle.2.1 cut (e 0) le_rfl
        (Nat.le_of_lt hBelow) (0 : Fin 1)
    rw [h1]
    exact hForward.trans ((hCrossSym (e 0)).symm.trans hBackward.symm)

/-- If the continuation with the tested cut deleted avoids one
forbidden asymmetric ordered pair, the original continuation
avoids it too, provided the full crossing is symmetric.

The forbidden pattern P itself supplies the asymmetry of any
realization; no symmetry is assumed of the arbitrary W away
from the tested cut. -/
theorem B3_no_new_asym_pair
    (C W : AgeTestModel 1 0 1)
    (cut : Nat)
    (hSocle : SameInitialL W C cut)
    (hCrossSym : ∀ x : Nat,
      C.binary cut x (0 : Fin 1) = C.binary x cut (0 : Fin 1))
    (hUpper : ∀ x, x ∈ W.carrier → cut < x →
      ∃ original : Nat,
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) original)
    (P : ForbiddenAtomicPattern 2 1 0 1)
    (hAsym : ∀ e : Fin 2 → Nat, W.Realizes P e →
      W.binary (e 0) (e 1) (0 : Fin 1) ≠
        W.binary (e 1) (e 0) (0 : Fin 1))
    (hDelete : ¬ ∃ e : Fin 2 → Nat,
      (W.withoutVertex cut).Realizes P e) :
    ¬ ∃ e : Fin 2 → Nat, W.Realizes P e := by
  rintro ⟨e,hCopy⟩
  have hAt : e 0 = cut ∨ e 1 = cut := by
    by_cases h0 : e 0 = cut
    · exact Or.inl h0
    · by_cases h1 : e 1 = cut
      · exact Or.inr h1
      · have hAway : ∀ a : Fin 2, e a ≠ cut := by
          intro a
          fin_cases a
          · exact h0
          · exact h1
        have hCopyDelete :=
          AgeTestModel.realizes_restrictCarrier W
            (fun x => x ≠ cut) P e hCopy hAway
        exact False.elim (hDelete ⟨e,hCopyDelete⟩)
  have hSym :=
    two_point_B3_cross_symmetric C W cut hSocle
      hCrossSym hUpper e hCopy.1 hCopy.2.1 hAt
  exact (hAsym e hCopy) hSym

/-- The actual forward and backward forbidden asymmetric pairs
are both excluded by complete directed type equality across the
tested cut; this is independent of the clique bound ell. -/
theorem B3_avoids_both_asym_patterns
    (C W : AgeTestModel 1 0 1)
    (cut : Nat)
    (hSocle : SameInitialL W C cut)
    (hCrossSym : ∀ x : Nat,
      C.binary cut x (0 : Fin 1) = C.binary x cut (0 : Fin 1))
    (hUpper : ∀ x, x ∈ W.carrier → cut < x →
      ∃ original : Nat,
        RelationalPrefixType.ofAgeModel W (cut+1) x =
          RelationalPrefixType.ofAgeModel C (cut+1) original)
    (hDeleteForward : ¬ ∃ e : Fin 2 → Nat,
      (W.withoutVertex cut).Realizes forwardAsymPattern e)
    (hDeleteBackward : ¬ ∃ e : Fin 2 → Nat,
      (W.withoutVertex cut).Realizes backwardAsymPattern e) :
    (¬ ∃ e : Fin 2 → Nat, W.Realizes forwardAsymPattern e) ∧
    (¬ ∃ e : Fin 2 → Nat, W.Realizes backwardAsymPattern e) := by
  constructor
  · apply B3_no_new_asym_pair C W cut hSocle hCrossSym
      hUpper forwardAsymPattern ?_ hDeleteForward
    intro e hCopy
    have h01 := hCopy.2.2.1
      (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have h10 := hCopy.2.2.1
      (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    have hForward : W.binary (e 0) (e 1) (0 : Fin 1) = true := by
      simpa [forwardAsymPattern] using h01
    have hBackward : W.binary (e 1) (e 0) (0 : Fin 1) = false := by
      simpa [forwardAsymPattern] using h10
    intro heq
    rw [hForward,hBackward] at heq
    cases heq
  · apply B3_no_new_asym_pair C W cut hSocle hCrossSym
      hUpper backwardAsymPattern ?_ hDeleteBackward
    intro e hCopy
    have h01 := hCopy.2.2.1
      (0 : Fin 2) (1 : Fin 2) (by decide) (0 : Fin 1)
    have h10 := hCopy.2.2.1
      (1 : Fin 2) (0 : Fin 2) (by decide) (0 : Fin 1)
    have hForward : W.binary (e 0) (e 1) (0 : Fin 1) = false := by
      simpa [backwardAsymPattern] using h01
    have hBackward : W.binary (e 1) (e 0) (0 : Fin 1) = true := by
      simpa [backwardAsymPattern] using h10
    intro heq
    rw [hForward,hBackward] at heq
    cases heq

end Kk
