import Kk.LaterSelectedMixedPools
import Mathlib.Tactic

/-!
# Exact finite decomposition of later selected neighbourhood-clique tests

A cardinal bound on each actual old interaction pool is sufficient
for safety, but it is not necessary: a large pool may have very few
edges. We now give a complete, executable alternative.

A directed q-clique in the full old neighbourhood is either wholly
unreserved, or uses some reserved block b and is entirely contained
in that block's actual interaction pool. Conversely, any clique in
one of these pools is also a clique in the full old neighbourhood.

Thus, under genuine cross-block nonedges, the full Boolean q-clique
checker is FALSE if and only if the checker on pure unreserved old
neighbours is FALSE and the *finite clique checker* on each block's
interaction pool is FALSE.

This avoids a global powerset search whenever the actual interface
pools are small, and it is stronger than bounding their sizes.
It does not assert that all these finite checks pass in the
proposed globally resolved Henson diary or determine its B3 closure.
-/

namespace Kk

/-- Fully executable q-clique checker on an arbitrary finite set P,
using explicit bounded (hence decidable) internal edge tests. -/
def finitePoolCliqueCheck
    (E : Nat → Nat → Bool) (q : Nat) (P : Finset Nat) : Bool :=
  decide ((P.powersetCard q).filter (fun s =>
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true)).Nonempty

theorem finitePoolCliqueCheck_true_iff
    (E : Nat → Nat → Bool) (q : Nat) (P : Finset Nat) :
    finitePoolCliqueCheck E q P = true ↔
      ∃ s : Finset Nat, s ⊆ P ∧ s.card = q ∧
        IsDirectedCliqueOn E s := by
  change decide ((P.powersetCard q).filter (fun s =>
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true)).Nonempty = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs⟩
    have hFilter := Finset.mem_filter.mp hs
    have hParts := Finset.mem_powersetCard.mp hFilter.1
    exact ⟨s, hParts.1, hParts.2, hFilter.2⟩
  · rintro ⟨s, hSub, hCard, hClique⟩
    exact ⟨s, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hSub, hCard⟩, hClique⟩⟩

theorem finitePoolCliqueCheck_false_iff
    (E : Nat → Nat → Bool) (q : Nat) (P : Finset Nat) :
    finitePoolCliqueCheck E q P = false ↔
      ¬ ∃ s : Finset Nat, s ⊆ P ∧ s.card = q ∧
        IsDirectedCliqueOn E s := by
  constructor
  · intro hFalse hBad
    have hTrue := (finitePoolCliqueCheck_true_iff E q P).2 hBad
    rw [hFalse] at hTrue
    cases hTrue
  · intro hNo
    cases h : finitePoolCliqueCheck E q P with
    | false => rfl
    | true =>
      exact False.elim (hNo
        ((finitePoolCliqueCheck_true_iff E q P).1 h))

/-- Every possible mixed-pool vertex actually belongs to the
complete old neighbourhood of the proposed new selected original. -/
theorem mixedBlockInteractionPool_subset_full_neighbourhood
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool) (b : Fin B) :
    mixedBlockInteractionPool E N B block neighbour b ⊆
      oldNeighbourSet N neighbour := by
  intro x hx
  have hRaw :
      x ∈ (Finset.range N).filter
        (fun y => neighbour y = true) := by
    rcases Finset.mem_union.mp hx with hReserved | hLinked
    · have hR := Finset.mem_filter.mp hReserved
      exact Finset.mem_filter.mpr ⟨hR.1, hR.2.1⟩
    · have hU := Finset.mem_filter.mp
        (Finset.mem_filter.mp hLinked).1
      exact Finset.mem_filter.mpr ⟨hU.1, hU.2.1⟩
  exact hRaw

/-- The complete neighbour-clique checker is *exactly* a finite
family of smaller tests: the pure unreserved neighbours and each
reserved block's actual mixing pool. This is not the weaker isolated
block shortcut: older unreserved vertices linked to the block
are explicitly included, as are their mutual old graph edges. -/
theorem finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools
    (E : Nat → Nat → Bool) (N q B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false) :
    finiteNeighbourCliqueCheck E N q neighbour = false ↔
      finiteNeighbourCliqueCheck E N q
        (fun x => if block x = none then neighbour x else false) = false ∧
      ∀ b : Fin B,
        finitePoolCliqueCheck E q
          (mixedBlockInteractionPool E N B block neighbour b) = false := by
  constructor
  · intro hFull
    have hNoFull :=
      (finiteNeighbourCliqueCheck_false_iff E N q neighbour).1 hFull
    constructor
    · apply (finiteNeighbourCliqueCheck_false_iff E N q
        (fun x => if block x = none then neighbour x else false)).2
      rintro ⟨s, hCard, hBound, hClique⟩
      apply hNoFull
      refine ⟨s, hCard, ?_, hClique⟩
      intro x hx
      obtain ⟨hLt, hPass⟩ := hBound x hx
      have hNeighbour : neighbour x = true := by
        by_cases hTag : block x = none
        · simpa [hTag] using hPass
        · simp [hTag] at hPass
      exact ⟨hLt, hNeighbour⟩
    · intro b
      apply (finitePoolCliqueCheck_false_iff E q
        (mixedBlockInteractionPool E N B block neighbour b)).2
      rintro ⟨s, hSub, hCard, hClique⟩
      apply hNoFull
      refine ⟨s, hCard, ?_, hClique⟩
      intro x hx
      have hActive :=
        mixedBlockInteractionPool_subset_full_neighbourhood
          E N B block neighbour b (hSub hx)
      have hFilter : x ∈ (Finset.range N).filter
          (fun y => neighbour y = true) := hActive
      have hProps := Finset.mem_filter.mp hFilter
      exact ⟨Finset.mem_range.mp hProps.1, hProps.2⟩
  · rintro ⟨hPlain, hPools⟩
    apply (finiteNeighbourCliqueCheck_false_iff E N q neighbour).2
    rintro ⟨s, hCard, hBound, hClique⟩
    have hWithin : ∀ x ∈ s, x < N := by
      intro x hx
      exact (hBound x hx).1
    have hNeighbour : ∀ x ∈ s, neighbour x = true := by
      intro x hx
      exact (hBound x hx).2
    by_cases hHasReserved : ∃ z ∈ s, ∃ b : Fin B, block z = some b
    · obtain ⟨z, hz, b, hzb⟩ := hHasReserved
      have hSub :=
        mixed_neighbourClique_subset_interaction_pool
          E N B block neighbour hCross s hWithin hNeighbour
          hClique z hz b hzb
      exact
        ((finitePoolCliqueCheck_false_iff E q
          (mixedBlockInteractionPool E N B block neighbour b)).1
            (hPools b)) ⟨s, hSub, hCard, hClique⟩
    · have hNone : ∀ x ∈ s, block x = none := by
        intro x hx
        cases hTag : block x with
        | none => rfl
        | some b => exact False.elim (hHasReserved ⟨x, hx, b, hTag⟩)
      have hPlainBad :
          HasNeighbourCliqueBelow E N q
            (fun x => if block x = none then neighbour x else false) := by
        refine ⟨s, hCard, ?_, hClique⟩
        intro x hx
        exact ⟨hWithin x hx, by simp [hNone x hx, hNeighbour x hx]⟩
      exact
        ((finiteNeighbourCliqueCheck_false_iff E N q
          (fun x => if block x = none then neighbour x else false)).1
            hPlain) hPlainBad

/-- Exact K_ell-free one-point extension criterion stated solely
using the genuine old unreserved checker and each small finite
block-interface checker, when older reserved blocks have no
cross-block edges. -/
theorem onePointGraph_cliqueFree_iff_exact_mixing_pools
    (E : Nat → Nat → Bool) (N ell B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false) :
    (¬ HasCliqueBelow
      (onePointGraphEdge E N neighbour) (N+1) ell) ↔
    finiteNeighbourCliqueCheck E N (ell-1)
      (fun x => if block x = none then neighbour x else false) = false ∧
    ∀ b : Fin B,
      finitePoolCliqueCheck E (ell-1)
        (mixedBlockInteractionPool E N B block neighbour b) = false := by
  exact (onePointGraph_cliqueFree_iff_finite_certificate
    E N ell neighbour hEll hOld).trans
    (finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools
      E N (ell-1) B block neighbour hCross)

/-- An exact collection of finite interface tests suffices to
realize a LATER selected original in the fixed Henson enumeration
even if older selected vertices already have edges to reserved
blocks. This is stronger than the cardinal-only interface test. -/
theorem henson_leftDense_realizes_later_selected_of_exact_mixing
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (N B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain :
      finiteNeighbourCliqueCheck E N (ell-1)
        (fun x => if block x = none then neighbour x else false) = false)
    (hExactPools : ∀ b : Fin B,
      finitePoolCliqueCheck E (ell-1)
        (mixedBlockInteractionPool E N B block neighbour b) = false) :
    ∃ v : Nat, N ≤ v ∧
      ∀ x, x < v →
        E x v = (if x < N then neighbour x else false) ∧
        E v x = (if x < N then neighbour x else false) := by
  have hFull := (finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools
    E N (ell-1) B block neighbour hCross).2 ⟨hPlain, hExactPools⟩
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense N neighbour hFull

/-- Five old vertices may all be neighbours of the proposed
selected original, even though only two reserved vertices
can participate in a mixed clique: noise vertices need not be
counted in each mixed interface. -/
def k4NoisyOldEdge (i j : Nat) : Bool :=
  decide ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))

def k4NoisyBlockTag (i : Nat) : Option (Fin 1) :=
  if i = 1 ∨ i = 2 then some 0 else none

def k4NoisyNewNeighbour (i : Nat) : Bool := decide (i < 5)

/-- The full old neighbourhood has five vertices (so the raw
cardinality test at threshold three fails), but the unique
mixed block-interface pool has only two vertices. -/
theorem k4NoisyMixedPool_small :
    (oldNeighbourSet 5 k4NoisyNewNeighbour).card = 5 ∧
    (mixedBlockInteractionPool k4NoisyOldEdge 5 1
      k4NoisyBlockTag k4NoisyNewNeighbour (0 : Fin 1)).card = 2 := by
  decide

/-- The exact interface algorithm certifies the full old
neighbourhood despite the large total number of old neighbours. -/
theorem k4NoisyOldNeighbourhood_certified :
    finiteNeighbourCliqueCheck k4NoisyOldEdge 5 3
      k4NoisyNewNeighbour = false := by
  apply (finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools
    k4NoisyOldEdge 5 3 1
    k4NoisyBlockTag k4NoisyNewNeighbour
    (by
      intro x y b c _ _ _ _ hbc
      fin_cases b
      fin_cases c
      exact (hbc rfl).elim)).2
  constructor
  · decide
  · intro b
    fin_cases b
    decide

end Kk
