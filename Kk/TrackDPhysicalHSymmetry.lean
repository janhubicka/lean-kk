import Kk.HensonEncoding
import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Track D: complete ordinary L symmetry of genuine finite numerical H+

English-first proof and hostile audit were committed BEFORE Lean:
docs/audits/2026-11-18-track-d-physical-H-symmetry-english.md

The numerical H ordinary-L generator has TWO orientations; if the
original base binary B is symmetric, swapping the positions simply
switches these branches. This does NOT make the auxiliary E symmetric.
-/

namespace Kk

open SuccessorTree.V10

/-- For ANY numerical positions x,y, including odd fake positions
and positions outside a finite carrier, a symmetric ORIGINAL
binary table gives a symmetric complete numerical H ordinary
binary relation. The auxiliary E is not part of this statement. -/
theorem hNumericBinary_symm_of_base_symm
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (hSym : ∀ i j : Nat, ∀ r : Fin d, B i j r = B j i r)
    (k x y : Nat) (r : Fin d) :
    hNumericBinary B k x y r = hNumericBinary B k y x r := by
  have hFlip : ∀ u v : Nat,
      HNumericCrossing B k u v r →
      HNumericCrossing B k v u r := by
    intro u v
    rintro ⟨i,j,q,m,hij,hq,hm,hgate,h⟩
    refine ⟨i,j,q,m,hij,hq,hm,hgate,?_⟩
    rcases h with ⟨hu,hv,hBit⟩ | ⟨hu,hv,hBit⟩
    · right
      refine ⟨hv,hu,?_⟩
      rw [← hSym i j r]
      exact hBit
    · left
      refine ⟨hv,hu,?_⟩
      rw [hSym i j r]
      exact hBit
  cases hx : hNumericBinary B k x y r with
  | false =>
    cases hy : hNumericBinary B k y x r with
    | false => rfl
    | true =>
      have hYX : HNumericCrossing B k y x r :=
        (hNumericBinary_true_iff B k y x r).mp hy
      have hX : hNumericBinary B k x y r = true :=
        (hNumericBinary_true_iff B k x y r).mpr (hFlip y x hYX)
      rw [hx] at hX
      cases hX
  | true =>
    cases hy : hNumericBinary B k y x r with
    | false =>
      have hXY : HNumericCrossing B k x y r :=
        (hNumericBinary_true_iff B k x y r).mp hx
      have hY : hNumericBinary B k y x r = true :=
        (hNumericBinary_true_iff B k y x r).mpr (hFlip x y hXY)
      rw [hy] at hY
      cases hY
    | true => rfl

/-- Genuine finite H+ over ANY symmetric Q graph has symmetric
ordinary L at all total numeric positions, independently of the
directed free-level E relation and beyond just source carrier pairs. -/
theorem finiteNumericH_graph_ordinary_L_symmetric
    (E : Nat → Nat → Bool) (hSym : ∀ i j, E i j = E j i)
    (k N x y : Nat) :
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
      x y (0 : Fin 1) =
    (finiteNumericH (normalizedGraphModel E) k N).L.binary
      y x (0 : Fin 1) := by
  change hNumericBinary (normalizedGraphModel E).binary k x y
    (0 : Fin 1) =
    hNumericBinary (normalizedGraphModel E).binary k y x
      (0 : Fin 1)
  apply hNumericBinary_symm_of_base_symm
  intro i j r
  fin_cases r
  change E i j = E j i
  exact hSym i j

#print axioms Kk.hNumericBinary_symm_of_base_symm
#print axioms Kk.finiteNumericH_graph_ordinary_L_symmetric

end Kk
