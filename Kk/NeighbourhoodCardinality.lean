import Kk.FiniteNeighbourCertificates
import Mathlib.Tactic

/-!
# A cardinality certificate for safe one-point extensions

The complete old neighbourhood of a proposed vertex can include
old selected originals, reserved clique vertices and dependent parameters.
The exact finite checker is already proved sound and complete.

A useful *constructive sufficient condition* is simpler: fewer than
ell-1 distinct old neighbours automatically rules out a forbidden
(ell-1)-clique. The actual neighbourhood, not merely a selected
graph-age shadow, is counted here.

This criterion will be used to insert an isolated auxiliary clique
block into any K_ell-free finite original prefix. It does NOT
settle admissibility of later selected vertices with potentially
many prescribed neighbours.
-/

namespace Kk

/-- The complete finite set of old vertices adjacent to the new one. -/
def oldNeighbourSet (N : Nat) (neighbour : Nat → Bool) : Finset Nat :=
  (Finset.range N).filter (fun x => neighbour x = true)

/-- No clique of size q exists in a finite neighbourhood with fewer
than q vertices, regardless of its internal edge table. -/
theorem no_neighbourClique_of_small_neighbour_set
    (E : Nat → Nat → Bool) (N q : Nat) (neighbour : Nat → Bool)
    (hSmall : (oldNeighbourSet N neighbour).card < q) :
    ¬ HasNeighbourCliqueBelow E N q neighbour := by
  rintro ⟨s, hCard, hBound, _⟩
  have hSubset : s ⊆ oldNeighbourSet N neighbour := by
    intro x hx
    change x ∈ (Finset.range N).filter
      (fun u => neighbour u = true)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hBound x hx).1, (hBound x hx).2⟩
  have hLe := Finset.card_le_card hSubset
  omega

/-- An executable negative complete-neighbourhood certificate follows
from a strict bound on the NUMBER of old neighbours. -/
theorem finiteNeighbourCliqueCheck_false_of_small_neighbour_set
    (E : Nat → Nat → Bool) (N q : Nat) (neighbour : Nat → Bool)
    (hSmall : (oldNeighbourSet N neighbour).card < q) :
    finiteNeighbourCliqueCheck E N q neighbour = false :=
  (finiteNeighbourCliqueCheck_false_iff E N q neighbour).2
    (no_neighbourClique_of_small_neighbour_set
      E N q neighbour hSmall)

/-- Safe one-point extension for a bounded total old neighbourhood.
This counts ALL previously present parameters, so it is strictly
stronger than checking the selected-front graph-age value. -/
theorem onePointGraph_safe_of_small_neighbour_set
    (E : Nat → Nat → Bool) (N ell : Nat)
    (neighbour : Nat → Bool)
    (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell)
    (hSmall : (oldNeighbourSet N neighbour).card < ell-1) :
    ¬ HasCliqueBelow
      (onePointGraphEdge E N neighbour) (N+1) ell := by
  exact (onePointGraph_cliqueFree_iff_finite_certificate
    E N ell neighbour hEll hOld).2
      (finiteNeighbourCliqueCheck_false_of_small_neighbour_set
        E N (ell-1) neighbour hSmall)

/-- A finite prescribed neighbour carrier Q bounds the complete
old neighbourhood. In particular, nonedges to every old vertex
outside Q are enough to reduce safety to the size of Q. -/
theorem onePointGraph_safe_of_prescribed_neighbour_carrier
    (E : Nat → Nat → Bool) (N ell : Nat)
    (neighbour : Nat → Bool) (Q : Finset Nat)
    (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell)
    (hAllowed : ∀ x, x < N → neighbour x = true → x ∈ Q)
    (hQ : Q.card < ell-1) :
    ¬ HasCliqueBelow
      (onePointGraphEdge E N neighbour) (N+1) ell := by
  have hSubset : oldNeighbourSet N neighbour ⊆ Q := by
    intro x hx
    have h := Finset.mem_filter.mp hx
    exact hAllowed x (Finset.mem_range.mp h.1) h.2
  have hCard := Finset.card_le_card hSubset
  exact onePointGraph_safe_of_small_neighbour_set
    E N ell neighbour hEll hOld (by omega)

end Kk
