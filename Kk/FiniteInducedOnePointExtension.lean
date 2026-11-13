import Kk.FiniteCliqueEmbeddingTransport
import Kk.ExactFiniteNeighbourRealization
import Mathlib.Tactic

/-!
# Genuine one-step Henson extension of a finite induced ordinary-L copy

English proof and hostile review committed first:
  docs/finite_induced_one_point_extension_english_audit.md

An abstract safe neighbour set S within an already faithfully
represented finite pattern P transfers by the exact induced-image
K_(ell-1)-free checker theorem. The fixed OnePointLeftDense E then
realizes a GENUINE later original v with the prescribed entire
symmetric old L-column and zero bits to ALL earlier indices not
representing P, including chronology gaps.

Theorem does NOT assert a whole infinite resolved copy, Kpt auxiliary
E closure, full corrected B3, or common labelled inverse-source orbit.
-/

namespace Kk

/-- One true physical later original extends a faithful finite
induced ordinary-L representation by an abstract new vertex n
with a certified symmetric safe neighbour set S.

All old-image edges match the prescribed target A table in BOTH
directions. All other preceding Henson indices (including any gaps)
are certified nonneighbours, not left as unknown graph atoms. -/
theorem onePointLeftDense_extend_finite_induced_copy
    (A E : Nat → Nat → Bool) (ell front n : Nat)
    (hell : 0 < ell)
    (hDense : OnePointLeftDense E ell)
    (hOld : ¬ HasCliqueBelow E front ell)
    (P S : Finset Nat) (hSP : S ⊆ P)
    (f : Nat → Nat)
    (hInj : Set.InjOn f ↑P)
    (hBelow : ∀ x ∈ P, f x < front)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      A x y = E (f x) (f y))
    (hNewForward : ∀ x ∈ P, A x n = decide (x ∈ S))
    (hNewSym : ∀ x ∈ P, A n x = A x n)
    (hSafe : finitePoolCliqueCheck A (ell-1) S = false) :
    ∃ v : Nat, front ≤ v ∧
      (∀ x ∈ P,
        E (f x) v = A x n ∧ E v (f x) = A n x) ∧
      (∀ z : Nat, z < v → z ∉ P.image f →
        E z v = false ∧ E v z = false) := by
  classical
  have hInjS : Set.InjOn f ↑S := by
    intro x hx y hy heq
    exact hInj (hSP hx) (hSP hy) heq
  have hEdgeS :
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        A x y = E (f x) (f y) := by
    intro x hx y hy hxy
    exact hEdge x (hSP hx) y (hSP hy) hxy
  have hImageSafe :
      finitePoolCliqueCheck E (ell-1) (S.image f) = false :=
    (finitePoolCliqueCheck_false_iff_induced_image
      A E S f hInjS hEdgeS (ell-1)).mp hSafe
  have hImageBelow : ∀ z ∈ S.image f, z < front := by
    intro z hz
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
    exact hxz ▸ (hBelow x (hSP hx))
  obtain ⟨v,hv,hColumn⟩ :=
    onePointLeftDense_realizes_exact_finite_neighbour_set
      E ell front hell hDense hOld
      (S.image f) hImageBelow hImageSafe
  refine ⟨v,hv,?_,?_⟩
  · intro x hx
    have hfx : f x < v := lt_of_lt_of_le (hBelow x hx) hv
    have hMember : f x ∈ S.image f ↔ x ∈ S := by
      constructor
      · intro hMem
        obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hMem
        have heq : y = x := hInj (hSP hy) hx hyx
        exact heq ▸ hy
      · intro hMem
        exact Finset.mem_image.mpr ⟨x,hMem,rfl⟩
    have hDec :
        decide (f x ∈ S.image f) = decide (x ∈ S) := by
      by_cases hxS : x ∈ S
      · have hImage := hMember.mpr hxS
        simp [hImage,hxS]
      · have hNotImage : f x ∉ S.image f :=
          fun hm => hxS (hMember.mp hm)
        simp [hNotImage,hxS]
    obtain ⟨hForward,hReverse⟩ := hColumn (f x) hfx
    constructor
    · exact (hForward.trans hDec).trans (hNewForward x hx).symm
    · exact ((hReverse.trans hDec).trans (hNewForward x hx).symm).trans
        (hNewSym x hx).symm
  · intro z hz hOutside
    have hNotS : z ∉ S.image f := by
      intro hS
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hS
      exact hOutside (Finset.mem_image.mpr ⟨x,hSP hx,hxz⟩)
    simpa [hNotS] using hColumn z hz

/-- For the actual normalized Henson forbidden family the old-prefix
K_ell-free condition needed by the previous theorem is derived
from avoidance, not postulated separately. OnePointLeftDense of
the fixed enumeration remains an explicit hypothesis. -/
theorem henson_leftDense_extend_finite_induced_copy
    (ell : Nat) (hell : 2 ≤ ell)
    (A E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front n : Nat)
    (P S : Finset Nat) (hSP : S ⊆ P)
    (f : Nat → Nat)
    (hInj : Set.InjOn f ↑P)
    (hBelow : ∀ x ∈ P, f x < front)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      A x y = E (f x) (f y))
    (hNewForward : ∀ x ∈ P, A x n = decide (x ∈ S))
    (hNewSym : ∀ x ∈ P, A n x = A x n)
    (hSafe : finitePoolCliqueCheck A (ell-1) S = false) :
    ∃ v : Nat, front ≤ v ∧
      (∀ x ∈ P,
        E (f x) v = A x n ∧ E v (f x) = A n x) ∧
      (∀ z : Nat, z < v → z ∉ P.image f →
        E z v = false ∧ E v z = false) := by
  exact onePointLeftDense_extend_finite_induced_copy
    A E ell front n (by omega) hDense
    (hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid front)
    P S hSP f hInj hBelow hEdge hNewForward hNewSym hSafe

#print axioms onePointLeftDense_extend_finite_induced_copy
#print axioms henson_leftDense_extend_finite_induced_copy

end Kk
