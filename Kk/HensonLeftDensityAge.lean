import Kk.HensonLeftDensityBridge
import Kk.HensonEncoding
import Mathlib.Tactic

/-!
# From the normalized Henson age to actual left-dense original vertices

The one-point left-density bridge uses K_ell-freeness of EVERY finite
prefix. The existing normalized Henson language already proves the
GLOBAL forbidden-family condition, expressed as absence of an
increasing K_ell copy (together with loop and asymmetric-pair
exclusion).

The key new step is to turn any finite directed clique of cardinality
ell into a genuinely strictly increasing Fin ell-indexed forbidden
clique, by the natural order embedding of a finite set.

Consequently, no extra per-prefix K_ell-free hypothesis is needed:
the verified Henson forbidden-family semantics supply it. Combined
with the one-point left-dense enumeration stipulated in the
manuscript, a negative full-neighbourhood certificate realizes
a genuine original index, and reserved blocks exist in the
unchanged ambient graph.

This does NOT supply a negative neighbourhood certificate for the
particular later selected vertices of the proposed resolved copy;
nor does it determine the full parameter-closed I1/I2/I3/B3 source.
-/

namespace Kk

/-- The global no-increasing-K_ell condition forbids cliques on
ANY finite initial segment. The finite clique is ordered using
the actual natural-number order, so no extra homogeneity or
induced-copy assumption is hidden. -/
theorem no_prefix_clique_of_no_increasing_clique
    (E : Nat → Nat → Bool) (ell : Nat)
    (hGlobal :
      ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
        (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true)) :
    ∀ N, ¬ HasCliqueBelow E N ell := by
  classical
  intro N
  rintro ⟨s, hCard, _hWithin, hClique⟩
  let f : Fin ell ↪o Nat := s.orderEmbOfFin hCard
  have hEdges : ∀ a b : Fin ell, a ≠ b →
      E (f a) (f b) = true := by
    intro a b hab
    have ha : f a ∈ s := s.orderEmbOfFin_mem hCard a
    have hb : f b ∈ s := s.orderEmbOfFin_mem hCard b
    have hne : f a ≠ f b := by
      intro heq
      exact hab (f.injective heq)
    exact hClique (f a) ha (f b) hb hne
  exact hGlobal ⟨(fun i => f i), f.strictMono, hEdges⟩

/-- The actual normalized forbidden-family predicate, not a
separately supplied graph-age axiom, implies K_ell-freeness of
every finite original prefix. -/
theorem hensonForbiddenFamily_no_prefix_cliques
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E)) :
    ∀ N, ¬ HasCliqueBelow E N ell := by
  exact no_prefix_clique_of_no_increasing_clique
    E ell (hensonForbiddenFamily_no_cliques ell hell E hAvoid)

/-- Under the manuscript's left-dense enumeration property,
a negative COMPLETE mixed-neighbourhood certificate at one
original stage gives a genuine later vertex of the fixed
normalized Henson graph. Its old and intervening columns,
in both orientations, are exact conclusions. -/
theorem henson_leftDense_realizes_certified_original
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front : Nat) (neighbour : Nat → Bool)
    (hCheck : finiteNeighbourCliqueCheck E front (ell-1)
      neighbour = false) :
    ∃ v : Nat, front ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = (if x < front then neighbour x else false) ∧
        E v x = (if x < front then neighbour x else false) := by
  exact onePointLeftDense_realizes_finite_certificate
    E ell front neighbour (by omega) hDense
    (hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid front) hCheck

/-- No extra small-set density or prefix-freeness axiom is
needed to choose a genuine reserved clique when the ambient
Henson graph avoids its actual normalized forbidden family and
its fixed enumeration is left-dense. -/
theorem henson_leftDense_exists_reserved_originals
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base r : Nat) (hR : r < ell) :
    ∃ S : Finset Nat,
      S.card = r ∧
      (∀ q ∈ S, base ≤ q) ∧
      IsDirectedCliqueOn E S ∧
      (∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false ∧ E q x = false) := by
  exact reserved_originals_of_onePointLeftDense
    E ell base r (by omega)
    (hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid) hDense hR

/-- The same existence theorem from the explicit graph hypotheses
used by the actual Henson AlgorithmRun developments: loops, symmetry
and the absence of an increasing K_ell copy. -/
theorem henson_leftDense_exists_reserved_of_graph_axioms
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (hDense : OnePointLeftDense E ell)
    (base r : Nat) (hR : r < ell) :
    ∃ S : Finset Nat,
      S.card = r ∧
      (∀ q ∈ S, base ≤ q) ∧
      IsDirectedCliqueOn E S ∧
      (∀ q ∈ S, ∀ x, x < q → x ∉ S →
        E x q = false ∧ E q x = false) := by
  have hAvoid :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops, hSym, hClique⟩
  exact henson_leftDense_exists_reserved_originals
    ell hell E hAvoid hDense base r hR

end Kk
