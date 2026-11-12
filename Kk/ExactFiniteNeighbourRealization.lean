import Kk.HensonLeftDensityAge
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Exact finite clique-neighbourhood criterion and genuine Henson realization

English proof and hostile audit committed FIRST:
  docs/exact_finite_neighbourhood_realization_english_audit.md

A finite proposed neighbour pool S lies below the full old front.
Its exact K_q-freeness is equivalent to the existing executable
complete-neighbourhood certificate for the characteristic column
x |-> decide (x in S). This is an IFF, not a cardinality shortcut.

Under genuine OnePointLeftDense and K_ell-free old prefix, a negative
certificate produces a REAL later original in the UNCHANGED fixed
graph, with exact both-directed adjacency to all of S and nonedges
to every old vertex outside S and every intervening gap original.
The normalized-Henson specialization uses genuine forbidden-family
avoidance and does not assume old-prefix-freeness separately.

This is one physical ORIGINAL extension step, not a full numerical-H+
E/parameter-closed B3 or common labelled inverse-source construction.
-/

namespace Kk

/-- An exact finite induced neighbour pool, with the whole proposed
column equal to its characteristic function, passes the executable
checker iff that very pool contains no directed q-clique. This holds
for q=0 and does not assume symmetry or graph universality. -/
theorem finiteNeighbourCliqueCheck_membership_iff_pool
    (E : Nat → Nat → Bool) (front q : Nat)
    (S : Finset Nat)
    (hBelow : ∀ x ∈ S, x < front) :
    finiteNeighbourCliqueCheck E front q (fun x => decide (x ∈ S)) = false ↔
      finitePoolCliqueCheck E q S = false := by
  constructor
  · intro hNeighbour
    apply (finitePoolCliqueCheck_false_iff E q S).2
    rintro ⟨s, hsS, hsCard, hsClique⟩
    have hNbr : HasNeighbourCliqueBelow E front q
        (fun x => decide (x ∈ S)) := by
      refine ⟨s, hsCard, ?_, hsClique⟩
      intro x hx
      have hxS := hsS hx
      refine ⟨hBelow x hxS, ?_⟩
      simpa only [decide_eq_true_eq] using hxS
    exact (finiteNeighbourCliqueCheck_false_iff E front q
      (fun x => decide (x ∈ S))).1 hNeighbour hNbr
  · intro hPool
    apply (finiteNeighbourCliqueCheck_false_iff E front q
      (fun x => decide (x ∈ S))).2
    rintro ⟨s, hsCard, hColumn, hsClique⟩
    have hsS : s ⊆ S := by
      intro x hx
      have hBit := (hColumn x hx).2
      simpa only [decide_eq_true_eq] using hBit
    exact (finitePoolCliqueCheck_false_iff E q S).1 hPool
      ⟨s, hsS, hsCard, hsClique⟩

/-- Exact finite K_(ell-1)-free neighbourhood condition suffices for
a genuine ONE-POINT extension in the SAME left-dense original graph.
Unlike the old small-set theorem, S may be arbitrarily large. The
returned v need not equal front, but every intervening gap is a
nonneighbour in BOTH orientations. -/
theorem onePointLeftDense_realizes_exact_finite_neighbour_set
    (E : Nat → Nat → Bool) (ell front : Nat)
    (hEll : 0 < ell)
    (hDense : OnePointLeftDense E ell)
    (hOld : ¬ HasCliqueBelow E front ell)
    (S : Finset Nat)
    (hBelow : ∀ x ∈ S, x < front)
    (hPoolFree : finitePoolCliqueCheck E (ell-1) S = false) :
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = decide (x ∈ S) ∧ E v x = decide (x ∈ S) := by
  have hCheck :
      finiteNeighbourCliqueCheck E front (ell-1)
        (fun x => decide (x ∈ S)) = false :=
    (finiteNeighbourCliqueCheck_membership_iff_pool
      E front (ell-1) S hBelow).2 hPoolFree
  obtain ⟨v,hv,hColumn⟩ :=
    onePointLeftDense_realizes_finite_certificate
      E ell front (fun x => decide (x ∈ S))
      hEll hDense hOld hCheck
  refine ⟨v,hv,?_⟩
  intro x hx
  have hTarget :
      (if x < front then decide (x ∈ S) else false) =
        decide (x ∈ S) := by
    by_cases hxf : x < front
    · simp [hxf]
    · have hNot : x ∉ S := by
        intro hxs
        exact hxf (hBelow x hxs)
      simp [hxf,hNot]
  obtain ⟨hForward,hReverse⟩ := hColumn x hx
  exact ⟨hForward.trans hTarget,hReverse.trans hTarget⟩

/-- Genuine normalized-Henson source version. The normalized
forbidden-family avoidance proves every old prefix is K_ell-free;
the exact finite clique capacity of S supplies the full certificate.
This does NOT independently prove the fixed enumeration is left dense:
OnePointLeftDense remains the explicit manuscript hypothesis. -/
theorem henson_leftDense_realizes_exact_finite_neighbour_set
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front : Nat)
    (S : Finset Nat)
    (hBelow : ∀ x ∈ S, x < front)
    (hPoolFree : finitePoolCliqueCheck E (ell-1) S = false) :
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = decide (x ∈ S) ∧ E v x = decide (x ∈ S) := by
  have hOld : ¬ HasCliqueBelow E front ell :=
    hensonForbiddenFamily_no_prefix_cliques ell hell E hAvoid front
  exact onePointLeftDense_realizes_exact_finite_neighbour_set
    E ell front (by omega) hDense hOld S hBelow hPoolFree

#print axioms finiteNeighbourCliqueCheck_membership_iff_pool
#print axioms onePointLeftDense_realizes_exact_finite_neighbour_set
#print axioms henson_leftDense_realizes_exact_finite_neighbour_set

end Kk
