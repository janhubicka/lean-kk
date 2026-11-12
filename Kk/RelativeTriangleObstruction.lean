import Kk.OnePointCliqueExtension
import Lean.Elab.Tactic.Omega

/-!
# Hostile finite regression: an abstract K3-free edge need not be
realizable over a prescribed old prefix with two required neighbours.

This is the concrete obstruction recorded in the English-first
extension-profile and boring-level audits. It uses the repository's
ACTUAL IsDirectedCliqueOn / HasCliqueBelow predicates on ordinary
binary L atoms, not auxiliary Kpt E incidence.

The theorem does not disprove the bounded resolved-copy programme;
it rejects the invalid inference that all abstract admissible
future cliques can be exposed over ANY fixed old neighbourhood.
-/

namespace Kk

/-- The three mutually adjacent vertices 0,1,2 form a genuine
three-clique under the actual symmetric directed Boolean L table. -/
theorem relative_triangle_from_full_old_column
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (h01 : E 0 1 = true) (h02 : E 0 2 = true)
    (h12 : E 1 2 = true) :
    HasCliqueBelow E 3 3 := by
  have h10 : E 1 0 = true := (hSym 1 0).trans h01
  have h20 : E 2 0 = true := (hSym 2 0).trans h02
  have h21 : E 2 1 = true := (hSym 2 1).trans h12
  refine ⟨Finset.range 3, by decide, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_range.mp hx
  · intro x hx y hy hxy
    have hx3 : x < 3 := Finset.mem_range.mp hx
    have hy3 : y < 3 := Finset.mem_range.mp hy
    have hxCases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    have hyCases : y = 0 ∨ y = 1 ∨ y = 2 := by omega
    rcases hxCases with rfl | rfl | rfl <;>
      rcases hyCases with rfl | rfl | rfl <;>
      simp_all

/-- Two vertices required to be neighbours of the same fixed old
vertex cannot themselves be joined by an L edge in the K3-free
three-vertex prefix. This forbids automatic relative realization
of an abstract two-vertex clique. -/
theorem relative_triangle_blocks_two_neighbours
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (hFree : ¬ HasCliqueBelow E 3 3)
    (h01 : E 0 1 = true) (h02 : E 0 2 = true) :
    E 1 2 = false := by
  cases h12 : E 1 2 with
  | false => rfl
  | true =>
    exact False.elim (hFree (relative_triangle_from_full_old_column E
      hSym h01 h02 h12))

#print axioms relative_triangle_from_full_old_column
#print axioms relative_triangle_blocks_two_neighbours

end Kk
