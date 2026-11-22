import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# Automatic saturated chains in a finite pointwise-ordered age class

The English proof and hostile audit were committed first in
`docs/track_b_automatic_cover_chain_english_audit_20261122.md`.

This result DOES NOT assume an input chain. The proof uses strong induction on
the total pointwise gap, splitting a non-cover interval at a genuine intermediate
age. It is order theoretic: no unsupported Kpt or physical diary claim.
-/

namespace Kk

universe u

/-- Sum of the pointwise gaps on a finite index type. -/
def ageCoordinateGap {ι : Type u} [Fintype ι]
    (lower upper : ι → Nat) : Nat :=
  (Finset.univ : Finset ι).sum (fun i => upper i - lower i)

/-- A nontrivial pointwise ordered interval has a positive total gap. -/
theorem ageCoordinateGap_pos_of_strict
    {ι : Type u} [Fintype ι]
    (lower upper : ι → Nat)
    (hLe : AgeLe lower upper) (hNe : lower ≠ upper) :
    0 < ageCoordinateGap lower upper := by
  classical
  have hWitness : ∃ i : ι, lower i < upper i := by
    by_contra hNone
    push_neg at hNone
    apply hNe
    funext i
    exact Nat.le_antisymm (hLe i) (hNone i)
  obtain ⟨i, hi⟩ := hWitness
  have hTerm : 0 < upper i - lower i := by omega
  have hSum : 0 <
      (Finset.univ : Finset ι).sum (fun j => upper j - lower j) := by
    apply Finset.sum_pos
    · intro j hj
      exact Nat.zero_le _
    · exact ⟨i, Finset.mem_univ i, hTerm⟩
  exact hSum

/-- Gap additivity across a pointwise intermediate age. -/
theorem ageCoordinateGap_split
    {ι : Type u} [Fintype ι]
    (lower mid upper : ι → Nat)
    (hLM : AgeLe lower mid) (hMU : AgeLe mid upper) :
    ageCoordinateGap lower upper =
      ageCoordinateGap lower mid + ageCoordinateGap mid upper := by
  classical
  unfold ageCoordinateGap
  calc
    (Finset.univ : Finset ι).sum (fun i => upper i - lower i) =
        (Finset.univ : Finset ι).sum
          (fun i => (mid i - lower i) + (upper i - mid i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hl := hLM i
      have hu := hMU i
      omega
    _ = (Finset.univ : Finset ι).sum (fun i => mid i - lower i) +
        (Finset.univ : Finset ι).sum (fun i => upper i - mid i) := by
      rw [Finset.sum_add_distrib]

/-- A chronological finite path of genuine covers. -/
inductive AgeCoverChain {ι : Type u}
    (IsAge : (ι → Nat) → Prop) :
    (ι → Nat) → (ι → Nat) → Prop where
  | refl (F : ι → Nat) : AgeCoverChain IsAge F F
  | step {F G H : ι → Nat}
      (hCover : AgeCover IsAge G F)
      (tail : AgeCoverChain IsAge G H) :
      AgeCoverChain IsAge F H

/-- Concatenate two chronological chains, keeping the common middle age. -/
theorem AgeCoverChain.trans
    {ι : Type u} {IsAge : (ι → Nat) → Prop}
    {F G H : ι → Nat}
    (first : AgeCoverChain IsAge F G)
    (second : AgeCoverChain IsAge G H) :
    AgeCoverChain IsAge F H := by
  induction first with
  | refl _ => exact second
  | step hCover tail ih =>
      exact AgeCoverChain.step hCover (ih second)

/-- Every ordered interval of genuine ages indexed by a FINITE type
has a finite saturated chain, without a supplied cover list.

The age predicate is arbitrary; no finiteness of its members is assumed:
the strictly decreasing natural pointwise-gap measure suffices. -/
theorem ageCoverChain_exists
    {ι : Type u} [Fintype ι]
    (IsAge : (ι → Nat) → Prop)
    (lower upper : ι → Nat)
    (hLower : IsAge lower) (hUpper : IsAge upper)
    (hLe : AgeLe lower upper) :
    AgeCoverChain IsAge upper lower := by
  classical
  have hAux : ∀ n : Nat, ∀ (L U : ι → Nat),
      ageCoordinateGap L U = n →
      IsAge L → IsAge U → AgeLe L U →
      AgeCoverChain IsAge U L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L U hGap hLA hUA hLU
        by_cases hEq : L = U
        · subst U
          exact AgeCoverChain.refl L
        · by_cases hNoIntermediate :
            ∀ M, IsAge M → AgeLe L M → AgeLe M U →
              M = L ∨ M = U
          · have hCover : AgeCover IsAge L U :=
              { lower_age := hLA
                upper_age := hUA
                le := hLU
                strict := hEq
                no_intermediate := hNoIntermediate }
            exact AgeCoverChain.step hCover (AgeCoverChain.refl L)
          · push_neg at hNoIntermediate
            obtain ⟨M, hMA, hLM, hMU, hMNeL, hMNeU⟩ :=
              hNoIntermediate
            have hPositiveLM : 0 < ageCoordinateGap L M :=
              ageCoordinateGap_pos_of_strict L M hLM hMNeL.symm
            have hPositiveMU : 0 < ageCoordinateGap M U :=
              ageCoordinateGap_pos_of_strict M U hMU hMNeU
            have hSplit := ageCoordinateGap_split L M U hLM hMU
            have hSmallerMU : ageCoordinateGap M U < n := by
              rw [← hGap]
              omega
            have hSmallerLM : ageCoordinateGap L M < n := by
              rw [← hGap]
              omega
            have hFirst : AgeCoverChain IsAge U M :=
              ih (ageCoordinateGap M U) hSmallerMU M U rfl hMA hUA hMU
            have hSecond : AgeCoverChain IsAge M L :=
              ih (ageCoordinateGap L M) hSmallerLM L M rfl hLA hMA hLM
            exact hFirst.trans hSecond
  exact hAux (ageCoordinateGap lower upper) lower upper rfl
    hLower hUpper hLe

/-- Specialization to actual normalized integer-witness graph ages. -/
theorem integerGraphAge_exists_saturated_chain
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hLower : IsIntegerGraphAge d ell lower)
    (hUpper : IsIntegerGraphAge d ell upper)
    (hLe : AgeLe lower upper) :
    AgeCoverChain (IsIntegerGraphAge d ell) upper lower :=
  ageCoverChain_exists (IsIntegerGraphAge d ell)
    lower upper hLower hUpper hLe

#print axioms Kk.ageCoordinateGap_pos_of_strict
#print axioms Kk.ageCoordinateGap_split
#print axioms Kk.AgeCoverChain.trans
#print axioms Kk.ageCoverChain_exists
#print axioms Kk.integerGraphAge_exists_saturated_chain

end Kk
