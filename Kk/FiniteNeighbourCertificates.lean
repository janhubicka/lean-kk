import Kk.OnePointCliqueExtension
import Mathlib.Tactic

/-!
# Finite executable certificates for mixed one-point neighbourhoods

The one-point extension criterion is mathematically exact, but
HasNeighbourCliqueBelow quantifies over all finite subsets of Nat.
This module supplies a bounded, executable certificate: enumerate
only the powerset-cardinality subsets of the ACTUAL finite old
carrier, and test their complete directed edge/neighbour conditions.

This lets later stages validate an explicit finite original/parameter
adjacency table with a kernel-checked computation, without treating
selected-front age equality or isolated block checks as sufficient.

The theorem checks a specified finite table. It does not construct
the globally resolved Henson copy or compare full B3 closures.
-/

namespace Kk

/-- All candidate cliques of size size in the complete prescribed
old neighbourhood, including older split/coding parameter vertices. -/
def finiteNeighbourCliqueCandidates
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) : Finset (Finset Nat) :=
  ((Finset.range N).powersetCard size).filter (fun s =>
    (∀ x ∈ s, neighbour x = true) ∧ IsDirectedCliqueOn E s)

/-- An executable Boolean test for a forbidden clique contained
in the complete old neighbourhood of the next vertex. -/
def finiteNeighbourCliqueCheck
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) : Bool :=
  decide (finiteNeighbourCliqueCandidates E N size neighbour).Nonempty

/-- The finite candidate enumeration is exactly the mathematical
neighbourhood-clique predicate, not merely a one-way diagnostic. -/
theorem finiteNeighbourCliqueCandidates_nonempty_iff
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) :
    (finiteNeighbourCliqueCandidates E N size neighbour).Nonempty ↔
      HasNeighbourCliqueBelow E N size neighbour := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    have hFilter := Finset.mem_filter.mp hs
    have hCardSet := Finset.mem_powersetCard.mp hFilter.1
    refine ⟨s, hCardSet.2, ?_, hFilter.2.2⟩
    intro x hx
    exact ⟨Finset.mem_range.mp (hCardSet.1 hx),
      hFilter.2.1 x hx⟩
  · rintro ⟨s, hCard, hBound, hClique⟩
    refine ⟨s, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hCard⟩
      intro x hx
      exact Finset.mem_range.mpr (hBound x hx).1
    · refine ⟨?_, hClique⟩
      intro x hx
      exact (hBound x hx).2

/-- Soundness and completeness of the executable positive test. -/
theorem finiteNeighbourCliqueCheck_true_iff
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) :
    finiteNeighbourCliqueCheck E N size neighbour = true ↔
      HasNeighbourCliqueBelow E N size neighbour := by
  simpa [finiteNeighbourCliqueCheck, decide_eq_true_eq] using
    (finiteNeighbourCliqueCandidates_nonempty_iff E N size neighbour)

/-- The negative result of the executable test is a complete
certificate of absence of cliques in the neighbourhood. -/
theorem finiteNeighbourCliqueCheck_false_iff
    (E : Nat → Nat → Bool) (N size : Nat)
    (neighbour : Nat → Bool) :
    finiteNeighbourCliqueCheck E N size neighbour = false ↔
      ¬ HasNeighbourCliqueBelow E N size neighbour := by
  constructor
  · intro hCheck hBad
    have hTrue :=
      (finiteNeighbourCliqueCheck_true_iff E N size neighbour).2 hBad
    rw [hCheck] at hTrue
    cases hTrue
  · intro hNo
    cases hCheck : finiteNeighbourCliqueCheck E N size neighbour with
    | false => rfl
    | true =>
      exact False.elim
        (hNo ((finiteNeighbourCliqueCheck_true_iff E N size neighbour).1 hCheck))

/-- The old initial segment cannot contain a larger finite clique
than its total number of available vertices. -/
theorem no_clique_below_of_small_carrier
    (E : Nat → Nat → Bool) (N ell : Nat) (hSmall : N < ell) :
    ¬ HasCliqueBelow E N ell := by
  rintro ⟨s, hCard, hBound, _⟩
  have hSub : s ⊆ Finset.range N := by
    intro x hx
    exact Finset.mem_range.mpr (hBound x hx)
  have hCardLe := Finset.card_le_card hSub
  simp only [Finset.card_range, hCard] at hCardLe
  omega

/-- One complete finite Boolean certificate suffices to establish
a safe one-point extension of a K_ell-free old graph. -/
theorem onePointGraph_cliqueFree_iff_finite_certificate
    (E : Nat → Nat → Bool) (N ell : Nat)
    (neighbour : Nat → Bool) (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell) :
    (¬ HasCliqueBelow
      (onePointGraphEdge E N neighbour) (N+1) ell) ↔
        finiteNeighbourCliqueCheck E N (ell-1) neighbour = false := by
  rw [onePointGraph_cliqueFree_iff E N ell neighbour hEll hOld]
  exact (finiteNeighbourCliqueCheck_false_iff E N (ell-1) neighbour).symm

end Kk
