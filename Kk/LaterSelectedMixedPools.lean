import Kk.MixedNeighbourhoodBlocks
import Kk.NeighbourhoodCardinality
import Kk.HensonLeftDensityAge
import Kk.K4NeighbourCertificate
import Mathlib.Tactic

/-!
# Later selected vertices: local mixed-neighbourhood interaction pools

The first-selected-after-isolated-block argument does not apply to
later selected vertices: an earlier selected vertex may already be
adjacent to reserved originals. For any complete old adjacency table
E, a future selected column neighbour, and a marking of reserved
originals by finite block identifiers, we construct a finite
*interaction pool* for each reserved block b.

The pool consists of (i) the reserved vertices of b to which the
future selected vertex passes, and (ii) the unreserved older
neighbours of the future selected vertex that actually have a
positive edge to AT LEAST ONE such active reserved vertex of b.
Both populations are computed from the ACTUAL old edge table.

When distinct reserved blocks are mutually nonadjacent, any
neighbourhood clique containing a reserved vertex lies in the
interaction pool of its unique block. Therefore an exact ordinary
test on the pure-unreserved neighbours plus a strict cardinality
bound for every interaction pool suffices to rule out an entire
K_(ell-1) in the new selected vertex's COMPLETE neighbourhood.

Unlike the first-block proof, this can apply after multiple older
selected vertices and reserved blocks already coexist, including
nontrivial mixed edges. It is a sufficient capacity criterion, NOT
an unconditional theorem that the manuscript's proposed recursive
gadget schedule satisfies these capacities or its B3 conditions.
-/

namespace Kk

/-- Reserved vertices of one block that are actually in the new
selected vertex's complete old neighbourhood. -/
def liveReservedBlock
    (N B : Nat) (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool) (b : Fin B) : Finset Nat :=
  (Finset.range N).filter
    (fun x => neighbour x = true ∧ block x = some b)

/-- All unreserved older neighbours of the new selected vertex,
including previously selected originals and split/coding parameters. -/
def liveUnreserved
    (N B : Nat) (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool) : Finset Nat :=
  (Finset.range N).filter
    (fun x => neighbour x = true ∧ block x = none)

/-- The unreserved neighbours genuinely linked to at least one live
reserved vertex of block b. The existential is over a FINITE set,
hence this is an executable finset, not an unrestricted Prop oracle. -/
def linkedUnreserved
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool) (b : Fin B) : Finset Nat :=
  (liveUnreserved N B block neighbour).filter
    (fun x => ∃ y ∈ liveReservedBlock N B block neighbour b,
      E x y = true)

/-- Complete possible interaction pool for a later selected vertex
and one previously reserved block, including genuine mixed links. -/
def mixedBlockInteractionPool
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool) (b : Fin B) : Finset Nat :=
  liveReservedBlock N B block neighbour b ∪
    linkedUnreserved E N B block neighbour b

/-- A neighbourhood clique containing a live reserved vertex z of
block b has no vertices outside the computed interaction pool of b.
This is the local geometric content of the block reduction; neither
the mixed edges nor older parameter vertices are discarded. -/
theorem mixed_neighbourClique_subset_interaction_pool
    (E : Nat → Nat → Bool) (N B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (s : Finset Nat)
    (hWithin : ∀ x ∈ s, x < N)
    (hNeighbour : ∀ x ∈ s, neighbour x = true)
    (hClique : IsDirectedCliqueOn E s)
    (z : Nat) (hz : z ∈ s)
    (b : Fin B) (hzb : block z = some b) :
    s ⊆ mixedBlockInteractionPool E N B block neighbour b := by
  intro x hx
  by_cases hReserved : ∃ c : Fin B, block x = some c
  · obtain ⟨c, hxc⟩ := hReserved
    have hEqual : c = b :=
      clique_reserved_blocks_agree E N B block hCross
        s hWithin hClique x z hx hz c b hxc hzb
    subst c
    apply Finset.mem_union.mpr
    left
    change x ∈ (Finset.range N).filter
      (fun y => neighbour y = true ∧ block y = some b)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hWithin x hx),
        ⟨hNeighbour x hx, hxc⟩⟩
  · have hxNone : block x = none := by
      cases hTag : block x with
      | none => rfl
      | some c => exact False.elim (hReserved ⟨c, hTag⟩)
    have hxz : x ≠ z := by
      intro heq
      have hContr : block x = some b := by
        rw [heq]
        exact hzb
      rw [hxNone] at hContr
      cases hContr
    have hzLive :
        z ∈ liveReservedBlock N B block neighbour b := by
      change z ∈ (Finset.range N).filter
        (fun y => neighbour y = true ∧ block y = some b)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hWithin z hz),
          ⟨hNeighbour z hz, hzb⟩⟩
    have hxLive :
        x ∈ liveUnreserved N B block neighbour := by
      change x ∈ (Finset.range N).filter
        (fun y => neighbour y = true ∧ block y = none)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hWithin x hx),
          ⟨hNeighbour x hx, hxNone⟩⟩
    have hxLink :
        x ∈ linkedUnreserved E N B block neighbour b := by
      change x ∈ (liveUnreserved N B block neighbour).filter
        (fun y => ∃ t ∈ liveReservedBlock N B block neighbour b,
          E y t = true)
      exact Finset.mem_filter.mpr
        ⟨hxLive, ⟨z, hzLive, hClique x hx z hz hxz⟩⟩
    exact Finset.mem_union.mpr (Or.inr hxLink)

/-- A finite capacity test sufficient for the FULL mixed
neighbourhood of a later selected vertex: test the pure-unreserved
neighbours, and count the actual potential mixing pool of each
previously reserved block. No assumption that earlier selected
vertices are nonadjacent to reserved blocks is made.

If the pool size for every block is less than q, a size-q clique
cannot use any reserved vertex. -/
theorem finiteNeighbourCliqueCheck_false_of_mixing_pools
    (E : Nat → Nat → Bool) (N q B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain :
      finiteNeighbourCliqueCheck E N q
        (fun x => if block x = none then neighbour x else false) = false)
    (hPools : ∀ b : Fin B,
      (mixedBlockInteractionPool E N B block neighbour b).card < q) :
    finiteNeighbourCliqueCheck E N q neighbour = false := by
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
    have hCardLe := Finset.card_le_card hSub
    have hSmall := hPools b
    omega
  · have hNone : ∀ x ∈ s, block x = none := by
      intro x hx
      cases hTag : block x with
      | none => rfl
      | some b =>
        exact False.elim (hHasReserved ⟨x, hx, b, hTag⟩)
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

/-- The full later-selected one-point extension is K_ell-free
whenever the old graph is K_ell-free, the unreserved-only checker
is negative and every old reserved-block mixing pool is small.
This is an actual finite graph theorem, not a diary classification. -/
theorem onePointGraph_safe_of_mixing_pools
    (E : Nat → Nat → Bool) (N ell B : Nat)
    (block : Nat → Option (Fin B))
    (neighbour : Nat → Bool)
    (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell)
    (hCross : ∀ x y (b c : Fin B),
      x < N → y < N →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain :
      finiteNeighbourCliqueCheck E N (ell-1)
        (fun x => if block x = none then neighbour x else false) = false)
    (hPools : ∀ b : Fin B,
      (mixedBlockInteractionPool E N B block neighbour b).card < ell-1) :
    ¬ HasCliqueBelow (onePointGraphEdge E N neighbour) (N+1) ell := by
  exact (onePointGraph_cliqueFree_iff_finite_certificate
    E N ell neighbour hEll hOld).2
      (finiteNeighbourCliqueCheck_false_of_mixing_pools
        E N (ell-1) B block neighbour hCross hPlain hPools)

/-- Under the established normalized Henson age and one-point left
density, the computable interaction-pool capacities realize a
GENUINE later selected original with all passing columns fixed.
Older reserved blocks may already have mixed incidences with earlier
selected vertices; the interface pool accounts for those incidences. -/
theorem henson_leftDense_realizes_later_selected_of_mixing_pools
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
    (hPools : ∀ b : Fin B,
      (mixedBlockInteractionPool E N B block neighbour b).card < ell-1) :
    ∃ v : Nat, N ≤ v ∧
      ∀ x, x < v →
        E x v = (if x < N then neighbour x else false) ∧
        E v x = (if x < N then neighbour x else false) := by
  have hCheck : finiteNeighbourCliqueCheck E N (ell-1)
      neighbour = false :=
    finiteNeighbourCliqueCheck_false_of_mixing_pools
      E N (ell-1) B block neighbour hCross hPlain hPools
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense N neighbour hCheck

end Kk
