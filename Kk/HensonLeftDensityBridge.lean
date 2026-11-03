import Kk.FreshReservedOriginals
import Kk.NeighbourhoodCardinality
import Mathlib.Tactic

/-!
# Bridge from the manuscript's left-dense one-point extensions

The KK-free manuscript fixes a left-dense enumeration of the Henson
graph: every admissible extension of an initial segment by one new
vertex can be represented by a later original, with no NEW positive
edges to the intervening original indices.

We record that *specific* property as OnePointLeftDense. It is an
explicit property of the fixed enumeration, not a consequence of
K_ell-freeness. For an undirected graph the two directed columns of
the new original coincide, hence both orientations are specified.

Theorem onePointLeftDense_realizes_finite_certificate turns the
kernel-checked finite full-neighbourhood Boolean certificate into
a genuine later original with exactly the prescribed old adjacency
and no positive intervening edges. More importantly, it derives the
SmallCliqueLeftDense hypothesis used by the reserved-original
construction (PR #43) from this single fixed-enumeration property
and the K_ell-free age of each finite prefix.

No assumption that the proposed *resolved* successor diary has
the required mixed-parameter certificates is made.
-/

namespace Kk

/-- Edge-table formulation of the one-point left-density requirement
fixed in the manuscript. A safe one-point extension at an initial
segment front is realized at an actual later original v; all edges
from v to the intervening interval [front,v) are forbidden.

For x<front the Boolean column is the prescribed neighbour value.
Symmetry and irreflexivity of the ambient graph are handled separately
by the K_ell-free Henson signature.
-/
def OnePointLeftDense (E : Nat → Nat → Bool) (ell : Nat) : Prop :=
  ∀ (front : Nat) (neighbour : Nat → Bool),
    ¬ HasCliqueBelow
      (onePointGraphEdge E front neighbour) (front+1) ell →
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = (if x < front then neighbour x else false) ∧
        E v x = (if x < front then neighbour x else false)

/-- A successful *complete* finite-neighbourhood certificate
produces an actual later original in the FIXED left-dense graph.
The two directions of every old atom and all intervening nonedges
are conclusions, not extra ad hoc edge assumptions. -/
theorem onePointLeftDense_realizes_finite_certificate
    (E : Nat → Nat → Bool) (ell front : Nat)
    (neighbour : Nat → Bool)
    (hEll : 0 < ell)
    (hDense : OnePointLeftDense E ell)
    (hOld : ¬ HasCliqueBelow E front ell)
    (hCheck :
      finiteNeighbourCliqueCheck E front (ell-1) neighbour = false) :
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = (if x < front then neighbour x else false) ∧
        E v x = (if x < front then neighbour x else false) := by
  have hExtension :
      ¬ HasCliqueBelow
        (onePointGraphEdge E front neighbour) (front+1) ell :=
    (onePointGraph_cliqueFree_iff_finite_certificate
      E front ell neighbour hEll hOld).2 hCheck
  exact hDense front neighbour hExtension

/-- The exact small-set complete-column hypothesis of the
reserved-original theorem follows from the *one-point*
left-density already stipulated in the manuscript, plus the
ambient K_ell-free age. No separate small-set density axiom
is needed for the proposed fixed enumeration. -/
theorem smallCliqueLeftDense_of_onePointLeftDense
    (E : Nat → Nat → Bool) (ell : Nat)
    (hEll : 0 < ell)
    (hFree : ∀ N, ¬ HasCliqueBelow E N ell)
    (hDense : OnePointLeftDense E ell) :
    SmallCliqueLeftDense E ell := by
  intro front S hBelow hSmall
  let neighbour : Nat → Bool := fun x => decide (x ∈ S)
  have hAllowed : ∀ x : Nat, x < front →
      neighbour x = true → x ∈ S := by
    intro x _ hx
    simpa only [neighbour, decide_eq_true_eq] using hx
  have hSafe :
      ¬ HasCliqueBelow
        (onePointGraphEdge E front neighbour) (front+1) ell :=
    onePointGraph_safe_of_prescribed_neighbour_carrier
      E front ell neighbour S hEll (hFree front) hAllowed hSmall
  obtain ⟨v, hv, hColumn⟩ := hDense front neighbour hSafe
  refine ⟨v, hv, ?_⟩
  intro x hx
  have hColumnEq :
      (if x < front then neighbour x else false) =
        decide (x ∈ S) := by
    by_cases hxf : x < front
    · simp [hxf, neighbour]
    · have hNot : x ∉ S := by
        intro hxs
        have hxOld := hBelow x hxs
        omega
      simp [hxf, hNot, neighbour]
  exact ⟨(hColumn x hx).1.trans hColumnEq,
    (hColumn x hx).2.trans hColumnEq⟩

/-- Genuine reserved original indices, in the *unchanged*
left-dense Henson edge table. This discharges the extra
SmallCliqueLeftDense hypothesis of PR #43 using exactly the
one-point property assumed by the manuscript.

The result is conditional on K_ell-freeness and OnePointLeftDense
of the fixed graph; it does not construct that enumeration from
Fraisse amalgamation or prove later mixed selected-vertex safety. -/
theorem reserved_originals_of_onePointLeftDense
    (E : Nat → Nat → Bool) (ell base r : Nat)
    (hEll : 0 < ell)
    (hFree : ∀ N, ¬ HasCliqueBelow E N ell)
    (hDense : OnePointLeftDense E ell)
    (hR : r < ell) :
    ∃ S : Finset Nat,
      S.card = r ∧
      (∀ q ∈ S, base ≤ q) ∧
      IsDirectedCliqueOn E S ∧
      (∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false ∧ E q x = false) := by
  exact smallCliqueLeftDense_exists_reserved E ell base r
    (smallCliqueLeftDense_of_onePointLeftDense
      E ell hEll hFree hDense) hR

end Kk
