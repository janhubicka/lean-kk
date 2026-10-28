import SuccessorTree.V10.I3SignatureCardinality
import Mathlib.Tactic

/-!
# Refined I3 signature bound when the forbidden pattern index is fixed

The general verified I3 signature count is the sum of
(M+1)^(size_i) over ALL indexed forbidden patterns. If all
genuine finite age witnesses at the selected levels have the
SAME forbidden-pattern index i0, their signatures lie in
just one fibre of the disjoint union. The already checked
signature-collision theorem remains valid in that fibre.

Therefore the count improves to (M+1)^(size_i0). There is
no new graph model, no signature injectivity axiom and no
assumption that all age failures use a given index unless
the caller explicitly proves it.

For K_ell-free graphs at positive generation, the clique-only
witness classification provides precisely the intended index
restriction once it is transported to the original-labelled
signature witnesses.
-/

namespace Kk

open SuccessorTree.V10

/-- Restricted form of the checked I3 signature capacity theorem:
one fixed forbidden-pattern index costs only one power of M+1,
not the sum of all pattern components. -/
theorem i3Levels_card_le_fixedPattern_capacity
    {k M db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (i0 : Fin k)
    (levels : Finset Nat)
    (hInitial : ∀ ell, ell ∈ levels →
      ∀ x, x ≤ ell → x ∈ C.carrier)
    (hWitness : ∀ ell, ell ∈ levels →
      ∃ w : I3OriginalSignatureWitness sizes patterns C original ell,
        w.familyIndex = i0) :
    levels.card ≤ (M+1) ^ (sizes i0) := by
  classical
  let CodeType := Σ i : Fin k, Fin (sizes i) → Option (Fin M)
  let Fibre := {c : CodeType // c.1 = i0}
  have hCardFibre : Fintype.card Fibre = (M+1) ^ (sizes i0) := by
    let equiv : Fibre ≃ (Fin (sizes i0) → Option (Fin M)) := {
      toFun := by
        intro c
        rcases c with ⟨⟨i,f⟩,hi⟩
        cases hi
        exact f
      invFun := fun f => ⟨⟨i0,f⟩,rfl⟩
      left_inv := by
        rintro ⟨⟨i,f⟩,hi⟩
        cases hi
        rfl
      right_inv := by
        intro f
        rfl
    }
    rw [Fintype.card_congr equiv]
    simp [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  by_cases hNonempty : levels.Nonempty
  · obtain ⟨first,hFirst⟩ := hNonempty
    let witness (ell : Nat) (h : ell ∈ levels) :
        I3OriginalSignatureWitness sizes patterns C original ell :=
      Classical.choose (hWitness ell h)
    have hFixed (ell : Nat) (h : ell ∈ levels) :
        (witness ell h).familyIndex = i0 :=
      Classical.choose_spec (hWitness ell h)
    let defaultCode : Fibre :=
      ⟨(witness first hFirst).code, hFixed first hFirst⟩
    let signature (ell : Nat) : Fibre :=
      if h : ell ∈ levels then
        ⟨(witness ell h).code, hFixed ell h⟩
      else defaultCode
    have hInjective : Set.InjOn signature (levels : Set Nat) := by
      intro a ha b hb hEq
      have haMem : a ∈ levels := Finset.mem_coe.mp ha
      have hbMem : b ∈ levels := Finset.mem_coe.mp hb
      have hCode :
          (witness a haMem).code = (witness b hbMem).code := by
        have hVal := congrArg Subtype.val hEq
        simpa only [signature, dif_pos haMem, dif_pos hbMem]
          using hVal
      by_contra hNe
      rcases lt_or_gt_of_ne hNe with hab | hba
      · exact (I3OriginalSignatureWitness.code_ne_of_lt
          sizes patterns C original a b hab (hInitial b hbMem)
          (witness a haMem) (witness b hbMem)) hCode
      · exact (I3OriginalSignatureWitness.code_ne_of_lt
          sizes patterns C original b a hba (hInitial a haMem)
          (witness b hbMem) (witness a haMem)) hCode.symm
    have hImage :
        (levels.image signature).card = levels.card :=
      Finset.card_image_iff.mpr hInjective
    calc
      levels.card = (levels.image signature).card := hImage.symm
      _ ≤ (Finset.univ : Finset Fibre).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = (M+1)^(sizes i0) := by
        simpa using hCardFibre
  · have hEmpty : levels = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hNonempty
    simp [hEmpty]

end Kk
