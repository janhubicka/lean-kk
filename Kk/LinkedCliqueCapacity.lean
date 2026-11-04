import Kk.LaterSelectedExactMixing
import Mathlib.Tactic

/-!
# Clique-capacity budget for selected originals with older reserved-block links

The English proof and hostile mathematical audit were committed FIRST in
`docs/linked_clique_capacity_english_audit.md`.

For a live reserved block R, let L be the unreserved old neighbours of a
proposed selected original that are actually adjacent to at least one live
reserved vertex of R. A clique in the mixed pool R ∪ L has size at most

    |R| + maximum directed-clique cardinality in L.

The second quantity is computed from the actual finite edge table, NOT
from the cardinality of L. It allows arbitrarily many older selected
originals to be linked to a reserved block if their mutual clique
capacity is small.

Together with PR #50's exact per-block mixing-pool decomposition, this
gives a sufficient complete old-neighbourhood certificate for a LATER
selected original, including genuine mixed edges to reserved originals.
Under the explicitly assumed Henson left-density property it also
realizes the later original in the unchanged ambient graph.

This does not prove that the proposed infinite resolved-copy schedule
satisfies the budgets, full parameter-closed B3, or common labelled orbit.
-/

namespace Kk

/-- The largest size of a directed clique in an ACTUAL finite
original-graph vertex set; computed by searching all finite subsets.
The empty subset supplies capacity zero. -/
def finiteDirectedCliqueCapacity
    (E : Nat → Nat → Bool) (P : Finset Nat) : Nat :=
  (P.powerset.filter (fun s =>
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true)).sup Finset.card

/-- Every directed clique inside P is bounded by the executable
clique capacity of P. No assumptions of symmetry or loop-freeness. -/
theorem directedClique_card_le_capacity
    (E : Nat → Nat → Bool) (P s : Finset Nat)
    (hSub : s ⊆ P)
    (hClique : IsDirectedCliqueOn E s) :
    s.card ≤ finiteDirectedCliqueCapacity E P := by
  have hs : s ∈
      P.powerset.filter (fun t =>
        ∀ x ∈ t, ∀ y ∈ t, x ≠ y → E x y = true) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hSub, hClique⟩
  exact Finset.le_sup (f := Finset.card) hs

/-- If R is the live reserved part and L is the genuine linked
unreserved part of an interaction pool, then the actual live
reserved CARDINALITY plus the linked unreserved CLIQUE CAPACITY
being strictly below q excludes every q-clique in R union L.
No false disjointness or block separation assumption is used here. -/
theorem finitePoolCliqueCheck_false_of_reserved_plus_link_capacity
    (E : Nat → Nat → Bool) (q : Nat)
    (R L : Finset Nat)
    (hBudget : R.card + finiteDirectedCliqueCapacity E L < q) :
    finitePoolCliqueCheck E q (R ∪ L) = false := by
  apply (finitePoolCliqueCheck_false_iff E q (R ∪ L)).2
  rintro ⟨s, hSub, hCard, hClique⟩
  have hCover : s ⊆ (s ∩ R) ∪ (s ∩ L) := by
    intro x hx
    rcases Finset.mem_union.mp (hSub hx) with hxR | hxL
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hx, hxR⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hx, hxL⟩))
  have hCoverCard : s.card ≤ ((s ∩ R) ∪ (s ∩ L)).card :=
    Finset.card_le_card hCover
  have hUnionCard :
      ((s ∩ R) ∪ (s ∩ L)).card ≤
        (s ∩ R).card + (s ∩ L).card :=
    Finset.card_union_le _ _
  have hReservedCard : (s ∩ R).card ≤ R.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hLinkedClique : IsDirectedCliqueOn E (s ∩ L) := by
    intro x hx y hy hxy
    exact hClique x (Finset.mem_inter.mp hx).1
      y (Finset.mem_inter.mp hy).1 hxy
  have hLinkedCard :
      (s ∩ L).card ≤ finiteDirectedCliqueCapacity E L :=
    directedClique_card_le_capacity E L (s ∩ L)
      Finset.inter_subset_right hLinkedClique
  omega

/-- An executable, genuinely mixed-neighbourhood safety criterion
for later selected vertices that see already existing reserved blocks.

The pure-unreserved q-clique test must be negative, and for EVERY
tagged reserved block the number of its live reserved neighbours
plus the maximum clique size among its genuine linked unreserved
neighbours must be below q. This can hold even when the linked
unreserved set itself is large. -/
theorem finiteNeighbourCliqueCheck_false_of_link_capacity
    (E : Nat → Nat → Bool) (N q B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E N q
      (fun x => if block x = none then neighbour x else false) = false)
    (hBudget : ∀ b : Fin B,
      (liveReservedBlock N B block neighbour b).card +
      finiteDirectedCliqueCapacity E
        (linkedUnreserved E N B block neighbour b) < q) :
    finiteNeighbourCliqueCheck E N q neighbour = false := by
  apply (finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools
    E N q B block neighbour hCross).2
  constructor
  · exact hPlain
  · intro b
    simpa only [mixedBlockInteractionPool] using
      finitePoolCliqueCheck_false_of_reserved_plus_link_capacity
        E q
        (liveReservedBlock N B block neighbour b)
        (linkedUnreserved E N B block neighbour b)
        (hBudget b)

/-- Genuine later selected ORIGINAL in the fixed Henson enumeration,
allowing old unreserved selected and coding parameters to have
actual positive links to old reserved blocks.

The certificate is derived first, then complete-column left-density
chooses the actual later vertex with all intervening zero bits. -/
theorem henson_leftDense_realizes_later_selected_of_link_capacity
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (N B : Nat) (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E N (ell-1)
      (fun x => if block x = none then neighbour x else false) = false)
    (hBudget : ∀ b : Fin B,
      (liveReservedBlock N B block neighbour b).card +
      finiteDirectedCliqueCapacity E
        (linkedUnreserved E N B block neighbour b) < ell-1) :
    ∃ v : Nat, N ≤ v ∧
      ∀ x, x < v →
        E x v = (if x < N then neighbour x else false) ∧
        E v x = (if x < N then neighbour x else false) := by
  have hFull := finiteNeighbourCliqueCheck_false_of_link_capacity
    E N (ell-1) B block neighbour hCross hPlain hBudget
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense N neighbour hFull

/-- Four-vertex K4 test: reserved 0 is adjacent to BOTH older
unreserved selected originals 1 and 2, but 1 and 2 are nonadjacent.
The proposed new selected original sees all three, and is safe.
This is genuine old-block mixing, not a freshly isolated block. -/
def k4OldLinksStarEdge (i j : Nat) : Bool :=
  decide ((i = 0 ∧ (j = 1 ∨ j = 2)) ∨
          (j = 0 ∧ (i = 1 ∨ i = 2)))

def k4OldLinksTriangleEdge (i j : Nat) : Bool :=
  decide ((i = 0 ∧ (j = 1 ∨ j = 2)) ∨
          (j = 0 ∧ (i = 1 ∨ i = 2)) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))

def k4OldLinksBlock (i : Nat) : Option (Fin 1) :=
  if i = 0 then some 0 else none

def k4OldLinksNextNeighbour (i : Nat) : Bool :=
  decide (i < 3)

/-- Linked old selected vertices are numerous, but nonadjacent
to each other. Their clique capacity is just one, not two. -/
theorem k4OldLinks_capacity_regression :
    (liveReservedBlock 3 1 k4OldLinksBlock
      k4OldLinksNextNeighbour (0 : Fin 1)).card = 1 ∧
    (linkedUnreserved k4OldLinksStarEdge 3 1
      k4OldLinksBlock k4OldLinksNextNeighbour (0 : Fin 1)).card = 2 ∧
    finiteDirectedCliqueCapacity k4OldLinksStarEdge
      (linkedUnreserved k4OldLinksStarEdge 3 1
        k4OldLinksBlock k4OldLinksNextNeighbour (0 : Fin 1)) = 1 := by
  decide

/-- The actual mixed-link old star is certified safely by the NEW
capacity theorem, not merely by executing a full powerset check. -/
theorem k4OldLinks_safe_by_capacity :
    finiteNeighbourCliqueCheck
      k4OldLinksStarEdge 3 3 k4OldLinksNextNeighbour = false := by
  apply finiteNeighbourCliqueCheck_false_of_link_capacity
    k4OldLinksStarEdge 3 3 1 k4OldLinksBlock
    k4OldLinksNextNeighbour
  · intro x y b c _ _ _ _ hbc
    fin_cases b
    fin_cases c
    exact (hbc rfl).elim
  · decide
  · intro b
    fin_cases b
    decide

/-- Add the missing positive edge between the two older linked
selected originals: the old neighbour set is now a triangle,
and the proposed new selected vertex creates a forbidden K4. -/
theorem k4OldLinks_bad_triangle_regression :
    finiteDirectedCliqueCapacity k4OldLinksTriangleEdge
      (linkedUnreserved k4OldLinksTriangleEdge 3 1
        k4OldLinksBlock k4OldLinksNextNeighbour (0 : Fin 1)) = 2 ∧
    finiteNeighbourCliqueCheck k4OldLinksTriangleEdge 3 3
      k4OldLinksNextNeighbour = true := by
  decide

end Kk
