import Kk.OrderedReservedBlockChain
import Mathlib.Tactic

/-!
# Last-neighbour isolation closes the complete finite selected column

The English proof and hostile boundary audit were committed first in
`docs/last_neighbour_isolation_english_audit.md`.

A forbidden clique in the neighbourhood of a proposed selected original
has a MAXIMUM original index. If that index is in a freshly isolated
reserved block of size < q, all earlier neighbours of the clique are
forced inside that same small block. Thus it cannot be a q-clique.

This argument does NOT require an assumed cross-block projection or a
selected-front graph-age equality: it checks the entire original graph.
A separate corollary combines this result with genuinely reserved Henson
originals and complete-column left density to realize one actual selected
original following any FINITE list of fresh isolated blocks.

The result does NOT apply to arbitrary later diary vertices whose passing
columns include previously selected originals AFTER old reserved blocks.
Nor does it resolve the full parameter-closed Algorithm 5.4 I1/I2/I3/B3
closure or a common labelled inverse-source orbit.
-/

namespace Kk

/-- A complete proposed selected neighbourhood is safe when every
fresh positive neighbour after the old cut belongs to some sufficiently
small clique block that is nonadjacent to ALL earlier outsiders.
The blocks need not be uniquely tagged, disjoint, or cross-free as a
separate assumption: the largest vertex of any potential clique does
all the work.

The original prefix passing column is checked with the ACTUAL complete
finite-neighbourhood Boolean checker, not a selected age shadow. -/
theorem finiteNeighbourCliqueCheck_false_of_last_isolated
    (E : Nat → Nat → Bool)
    (base front q : Nat) (U : Finset Nat)
    (oldNeighbour : Nat → Bool)
    (hq : 0 < q)
    (hOld : finiteNeighbourCliqueCheck E base q oldNeighbour = false)
    (hIso : ∀ y ∈ U, ∃ S : Finset Nat,
      y ∈ S ∧ S.card < q ∧
        (∀ x : Nat, x < y → x ∉ S → E x y = false)) :
    finiteNeighbourCliqueCheck E front q
      (fun x => if x < base then oldNeighbour x else decide (x ∈ U)) =
        false := by
  classical
  apply (finiteNeighbourCliqueCheck_false_iff E front q
    (fun x => if x < base then oldNeighbour x else decide (x ∈ U))).2
  rintro ⟨s, hCard, hBound, hClique⟩
  have hsNonempty : s.Nonempty :=
    Finset.card_pos.mp (by omega)
  let y : Nat := s.max' hsNonempty
  have hyMem : y ∈ s := Finset.max'_mem s hsNonempty
  have hyPass :
      (if y < base then oldNeighbour y else decide (y ∈ U)) = true :=
    (hBound y hyMem).2
  by_cases hyOld : y < base
  · have hBad : HasNeighbourCliqueBelow E base q oldNeighbour := by
      refine ⟨s, hCard, ?_, hClique⟩
      intro x hx
      have hLe : x ≤ y := Finset.le_max' s x hx
      have hxOld : x < base := by omega
      have hxPass := (hBound x hx).2
      exact ⟨hxOld, by simpa [hxOld] using hxPass⟩
    exact ((finiteNeighbourCliqueCheck_false_iff E base q oldNeighbour).1
      hOld) hBad
  · have hyU : y ∈ U := by
      have hDecision : decide (y ∈ U) = true := by
        simpa [hyOld] using hyPass
      simpa only [decide_eq_true_eq] using hDecision
    obtain ⟨S, hyS, hSmall, hEarlierOutside⟩ := hIso y hyU
    have hSub : s ⊆ S := by
      intro x hx
      by_cases hEq : x = y
      · simpa [hEq] using hyS
      · have hLe : x ≤ y := Finset.le_max' s x hx
        have hLt : x < y := by omega
        by_contra hxNot
        have hZero : E x y = false :=
          hEarlierOutside x hLt hxNot
        have hOne : E x y = true :=
          hClique x hx y hyMem hEq
        rw [hZero] at hOne
        cases hOne
    have hCardLe := Finset.card_le_card hSub
    omega

/-- The finite union of actual blocks. Repeated empty blocks cause
no difficulties; no false uniqueness or partition hypothesis is needed. -/
def reservedBlocksUnion (blocks : List (Finset Nat)) : Finset Nat :=
  blocks.toFinset.biUnion (fun S => S)

theorem mem_reservedBlocksUnion
    (blocks : List (Finset Nat)) (y : Nat) :
    y ∈ reservedBlocksUnion blocks ↔
      ∃ S ∈ blocks, y ∈ S := by
  classical
  simp [reservedBlocksUnion]

/-- One genuine selected original can be chosen AFTER an arbitrary
finite ordered family of FRESH isolated reserved cliques. The full
new neighbour certificate follows from the maximal-neighbour argument,
not from an assumed safe mixed-parameter test.

All reserved indices and the selected original are indices of the SAME
unchanged original Henson enumeration. All passing bits over the
intervening unreserved gap interval are explicitly zero.

**Scope boundary:** the theorem does not iterate through previously
selected vertices that are later than older reserved blocks. Those
stages still need PR #50's exact mixed interaction-pool certificates. -/
theorem henson_leftDense_selected_after_fresh_block_family
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base : Nat) (sizes : List Nat)
    (hSmall : ∀ r ∈ sizes, r < ell-1)
    (oldNeighbour : Nat → Bool)
    (hOldCheck :
      finiteNeighbourCliqueCheck E base (ell-1) oldNeighbour = false) :
    ∃ (blocks : List (Finset Nat)) (front v : Nat),
      blocks.map Finset.card = sizes ∧
      blocks.Pairwise (OrderedReservedBlockCrossNonedges E) ∧
      (∀ S ∈ blocks,
        (∀ x ∈ S, base ≤ x ∧ x < front) ∧
        IsDirectedCliqueOn E S ∧
        (∀ y ∈ S, ∀ x, x < y → x ∉ S →
          E x y = false ∧ E y x = false)) ∧
      front ≤ v ∧
      (∀ x : Nat, x < v →
        E x v =
          (if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion blocks))
           else false) ∧
        E v x =
          (if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion blocks))
           else false)) := by
  classical
  have hReserve : ∀ r ∈ sizes, r < ell := by
    intro r hr
    have := hSmall r hr
    omega
  obtain ⟨blocks, hCards, hProps, hCross⟩ :=
    henson_leftDense_ordered_reserved_blocks
      ell hell E hAvoid hDense sizes hReserve base
  let U : Finset Nat := reservedBlocksUnion blocks
  let front : Nat := max base (U.sup (fun z : Nat => z) + 1)
  have hUFront : ∀ y ∈ U, y < front := by
    intro y hy
    have hSup : y ≤ U.sup (fun z : Nat => z) :=
      Finset.le_sup (f := fun z : Nat => z) hy
    dsimp [front]
    omega
  have hLastIsolated : ∀ y ∈ U, ∃ S : Finset Nat,
      y ∈ S ∧ S.card < ell-1 ∧
        (∀ x : Nat, x < y → x ∉ S → E x y = false) := by
    intro y hy
    obtain ⟨S, hS, hyS⟩ :=
      (mem_reservedBlocksUnion blocks y).1 hy
    obtain ⟨_hAfter, _hClique, hIso⟩ := hProps S hS
    have hCardMem : S.card ∈ sizes := by
      rw [← hCards]
      exact List.mem_map.mpr ⟨S, hS, rfl⟩
    exact ⟨S, hyS, hSmall S.card hCardMem,
      fun x hLt hOutside => (hIso y hyS x hLt hOutside).1⟩
  have hFullCheck :
      finiteNeighbourCliqueCheck E front (ell-1)
        (fun x => if x < base then oldNeighbour x
          else decide (x ∈ U)) = false :=
    finiteNeighbourCliqueCheck_false_of_last_isolated
      E base front (ell-1) U oldNeighbour
      (by omega) hOldCheck hLastIsolated
  obtain ⟨v, hv, hColumn⟩ :=
    henson_leftDense_realizes_certified_original
      ell hell E hAvoid hDense front
      (fun x => if x < base then oldNeighbour x
        else decide (x ∈ U)) hFullCheck
  have hBlockProps : ∀ S ∈ blocks,
      (∀ x ∈ S, base ≤ x ∧ x < front) ∧
      IsDirectedCliqueOn E S ∧
      (∀ y ∈ S, ∀ x, x < y → x ∉ S →
        E x y = false ∧ E y x = false) := by
    intro S hS
    obtain ⟨hAfter, hClique, hIso⟩ := hProps S hS
    refine ⟨?_, hClique, hIso⟩
    intro x hx
    have hxU : x ∈ U :=
      (mem_reservedBlocksUnion blocks x).2 ⟨S, hS, hx⟩
    exact ⟨hAfter x hx, hUFront x hxU⟩
  refine ⟨blocks, front, v, hCards, hCross, hBlockProps, hv, ?_⟩
  intro x hx
  simpa only [U] using hColumn x hx

end Kk
