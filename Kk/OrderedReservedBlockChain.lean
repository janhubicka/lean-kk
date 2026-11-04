import Kk.HensonLeftDensityAge
import Mathlib.Tactic

/-!
# Actual finite chains of mutually nonadjacent reserved original cliques

The English proof and an independent adversarial review were committed
FIRST in `docs/ordered_reserved_blocks_english_audit.md`.

This module builds arbitrarily many FINITE reserved blocks inside ONE fixed
enumerated Henson graph, from the normalized forbidden-family avoidance
condition and the separately stated complete-column left-density property.
It uses the real original indices; it does not alter the adjacency table.

Every later block is isolated from earlier outsiders. Consequently any two
different reserved blocks are mutually nonadjacent in both directions,
even when gap vertices occur between chosen original indices.

This closes the cross-block *original nonedge* existence obligation.
It does NOT show that the proposed global selected-vertex schedule passes its
mixed-neighbourhood certificates, or identify full I1/I2/I3/B3
parameter closures or a common labelled inverse-source orbit.
-/

namespace Kk

/-- A block `S` comes strictly before `T`, and all cross-block
edges in the ORIGINAL Boolean table are absent in both orientations. -/
def OrderedReservedBlockCrossNonedges
    (E : Nat → Nat → Bool) (S T : Finset Nat) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T,
    x < y ∧ E x y = false ∧ E y x = false

/-- Any finite ordered list of sizes `r < ell` is realized by actual
isolated original cliques of those sizes. Each later original is
nonadjacent to every earlier outsider (including enumeration gaps);
the blocks are ordered and mutually nonadjacent.

For attaching a later SELECTED vertex to an entire block, one needs
the STRONGER bound `r < ell-1`. This theorem only reserves blocks,
without claiming the selected extension is safe. -/
theorem henson_leftDense_ordered_reserved_blocks
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell) :
    ∀ sizes : List Nat,
      (∀ r ∈ sizes, r < ell) →
      ∀ base : Nat,
      ∃ blocks : List (Finset Nat),
        blocks.map Finset.card = sizes ∧
        (∀ S ∈ blocks,
          (∀ q ∈ S, base ≤ q) ∧
          IsDirectedCliqueOn E S ∧
          (∀ q ∈ S, ∀ x, x < q → x ∉ S →
            E x q = false ∧ E q x = false)) ∧
        blocks.Pairwise (OrderedReservedBlockCrossNonedges E) := by
  intro sizes
  induction sizes with
  | nil =>
    intro _ base
    refine ⟨[], rfl, ?_, List.Pairwise.nil⟩
    intro S hS
    simp at hS
  | cons r rest ih =>
    intro hSmall base
    have hr : r < ell := hSmall r (by simp)
    have hRest : ∀ t ∈ rest, t < ell := by
      intro t ht
      exact hSmall t (by simp [ht])
    obtain ⟨S, hCard, hAfter, hClique, hIso⟩ :=
      henson_leftDense_exists_reserved_originals
        ell hell E hAvoid hDense base r hr
    let nextBase : Nat := max base (S.sup (fun z : Nat => z) + 1)
    obtain ⟨tail, hTailSizes, hTailProps, hTailPairwise⟩ :=
      ih hRest nextBase
    refine ⟨S :: tail, ?_, ?_, ?_⟩
    · simp [hCard, hTailSizes]
    · intro T hT
      rcases List.mem_cons.mp hT with hEq | hTail
      · subst T
        exact ⟨hAfter, hClique, hIso⟩
      · obtain ⟨hTailAfter, hTailClique, hTailIso⟩ :=
          hTailProps T hTail
        refine ⟨?_, hTailClique, hTailIso⟩
        intro y hy
        have hyLower : nextBase ≤ y := hTailAfter y hy
        dsimp [nextBase] at hyLower
        omega
    · apply List.Pairwise.cons
      · intro T hT
        intro x hx y hy
        have hxSup : x ≤ S.sup (fun z : Nat => z) :=
          Finset.le_sup (f := fun z : Nat => z) hx
        have hyLower : nextBase ≤ y := (hTailProps T hT).1 y hy
        have hxy : x < y := by
          dsimp [nextBase] at hyLower
          omega
        have hxNotT : x ∉ T := by
          intro hxT
          have hxLower : nextBase ≤ x := (hTailProps T hT).1 x hxT
          dsimp [nextBase] at hxLower
          omega
        have hEdges : E x y = false ∧ E y x = false :=
          (hTailProps T hT).2.2 y hy x hxy hxNotT
        exact ⟨hxy, hEdges⟩
      · exact hTailPairwise

/-- The output's pairwise predicate gives the concrete directed
cross-block nonedges whenever two block positions are ordered. -/
theorem ordered_reserved_block_cross_nonedges_of_lt
    (E : Nat → Nat → Bool) (blocks : List (Finset Nat))
    (hCross : blocks.Pairwise (OrderedReservedBlockCrossNonedges E))
    (i j : Fin blocks.length) (hij : i < j)
    (x y : Nat) (hx : x ∈ blocks.get i) (hy : y ∈ blocks.get j) :
    x < y ∧ E x y = false ∧ E y x = false := by
  exact (hCross.rel_get_of_lt hij) x hx y hy


/-- Adversarial boundary regression: a reserved clique of size
ell-1 already makes the prescribed selected-vertex column unsafe
when the new vertex is adjacent to the whole clique.
The reservation theorem's weaker r<ell bound MUST NOT be
silently reused as the selected-extension safety bound. -/
theorem full_reserved_block_forbids_selected_column
    (E : Nat → Nat → Bool) (ell N : Nat)
    (S : Finset Nat)
    (hCard : S.card = ell-1)
    (hBelow : ∀ x ∈ S, x < N)
    (hClique : IsDirectedCliqueOn E S)
    (neighbour : Nat → Bool)
    (hPass : ∀ x ∈ S, neighbour x = true) :
    finiteNeighbourCliqueCheck E N (ell-1) neighbour = true := by
  apply (finiteNeighbourCliqueCheck_true_iff E N (ell-1) neighbour).2
  refine ⟨S, hCard, ?_, hClique⟩
  intro x hx
  exact ⟨hBelow x hx, hPass x hx⟩

end Kk
