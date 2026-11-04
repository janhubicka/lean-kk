import Kk.LinkedCliqueCapacity
import Kk.LastNeighbourIsolation
import Mathlib.Tactic

/-!
# One genuine later selected stage with old-block links AND fresh clique blocks

The mathematical proof and independent hostile audit were committed FIRST
in `docs/linked_and_fresh_stage_english_audit.md` before this Lean file.

PR #54 certifies that a prescribed next selected original's entire old
neighbourhood is K_(ell-1)-free, allowing true positive links to old
reserved blocks through a computable *linked-unreserved clique-capacity*
budget. PR #52 then reserves an arbitrary finite family of NEW genuine
isolated clique blocks and chooses a subsequent real selected original.

The additional proved invariant is that every NEW reserved block original
has both-directed nonedges to ALL earlier original indices, including
older reserved, selected, coding/split parameter, and gap indices.

This theorem handles one complete geometric successor stage. It does
NOT prove that every stage of the prescribed unbounded macrodiary
passes the displayed old budgets. It says nothing about full
parameter-closed I1/I2/I3/B3 or the common labelled inverse-source orbit.
-/

namespace Kk

/-- One stage with previously reserved blocks and their genuine links
to older selected/parameter originals, followed by an arbitrary finite
family of NEW isolated reserved cliques and a genuinely later selected
original.

The result additionally proves that every new reserved clique vertex
is nonadjacent (in BOTH directions) to EVERY old original below base.
Consequently the previous cross-block nonedge invariant is preserved
across this fresh block insertion. There is no retroactive graph edit. -/
theorem henson_leftDense_later_selected_after_fresh_blocks_of_link_capacity
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base B : Nat)
    (block : Nat → Option (Fin B))
    (oldNeighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < base → y < base →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E base (ell-1)
      (fun x => if block x = none then oldNeighbour x else false) = false)
    (hBudget : ∀ b : Fin B,
      (liveReservedBlock base B block oldNeighbour b).card +
      finiteDirectedCliqueCapacity E
        (linkedUnreserved E base B block oldNeighbour b) < ell-1)
    (sizes : List Nat) (hSmall : ∀ r ∈ sizes, r < ell-1) :
    ∃ (fresh : List (Finset Nat)) (front v : Nat),
      fresh.map Finset.card = sizes ∧
      fresh.Pairwise (OrderedReservedBlockCrossNonedges E) ∧
      (∀ S ∈ fresh,
        (∀ x ∈ S, base ≤ x ∧ x < front) ∧
        IsDirectedCliqueOn E S ∧
        (∀ y ∈ S, ∀ x, x < y → x ∉ S →
          E x y = false ∧ E y x = false)) ∧
      (∀ S ∈ fresh, ∀ x, x < base → ∀ y ∈ S,
        E x y = false ∧ E y x = false) ∧
      front ≤ v ∧
      (∀ x : Nat, x < v →
        E x v =
          (if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion fresh))
           else false) ∧
        E v x =
          (if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion fresh))
           else false)) := by
  classical
  have hOldCheck :
      finiteNeighbourCliqueCheck E base (ell-1) oldNeighbour = false :=
    finiteNeighbourCliqueCheck_false_of_link_capacity
      E base (ell-1) B block oldNeighbour hCross hPlain hBudget
  obtain ⟨fresh, front, v, hCards, hPair, hProps, hV, hColumn⟩ :=
    henson_leftDense_selected_after_fresh_block_family
      ell hell E hAvoid hDense base sizes hSmall
      oldNeighbour hOldCheck
  refine ⟨fresh, front, v, hCards, hPair, hProps, ?_, hV, hColumn⟩
  intro S hS x hx y hy
  have hyBase : base ≤ y := ((hProps S hS).1 y hy).1
  have hxy : x < y := by omega
  have hxNot : x ∉ S := by
    intro hxS
    have hxBase : base ≤ x := ((hProps S hS).1 x hxS).1
    omega
  exact (hProps S hS).2.2 y hy x hxy hxNot

end Kk
