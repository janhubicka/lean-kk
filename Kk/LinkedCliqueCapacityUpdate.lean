import Kk.LinkedCliqueCapacity
import Mathlib.Tactic

/-!
# Incremental capacity of genuine linked old-original vertices

The English proof and hostile audit were committed FIRST in
`docs/clique_capacity_insert_english_audit.md` before this file.

For a new unreserved original v and finite linked old set L, the
maximum directed clique size in L ∪ {v} is computed EXACTLY from
the old capacity and the subpool of vertices with BOTH directed
edges to v. This is a mathematical update of the actual old
edge table, not a selected-age shadow or a corrected-B3 transfer.

The per-old-block PR #54 budget can thus be updated without a
wasteful +1 cost for every new linked vertex. If v has no edges
into L and cap(L)≥1, there is no growth at all.

This does NOT prove that the intended macrodiary leaves live
reserved sets fixed or that all future selected vertices pass
these budgets. Full I1/I2/I3/B3 and common labelled orbit remain open.
-/

namespace Kk

/-- The old linked originals which are compatible with a new v
in BOTH directions of the actual directed Boolean edge table. -/
def mutualLinkedNeighbours
    (E : Nat → Nat → Bool) (L : Finset Nat) (v : Nat) :
    Finset Nat :=
  L.filter (fun x => E x v = true ∧ E v x = true)

/-- Capacity is monotone under inclusion of original sets. -/
theorem finiteDirectedCliqueCapacity_mono
    (E : Nat → Nat → Bool) (P Q : Finset Nat)
    (hPQ : P ⊆ Q) :
    finiteDirectedCliqueCapacity E P ≤
      finiteDirectedCliqueCapacity E Q := by
  classical
  unfold finiteDirectedCliqueCapacity
  apply Finset.sup_le
  intro s hs
  have hPieces := Finset.mem_filter.mp hs
  have hSub : s ⊆ Q :=
    (Finset.mem_powerset.mp hPieces.1).trans hPQ
  exact directedClique_card_le_capacity E Q s hSub hPieces.2

/-- Any directed clique in L plus one vertex v either avoids v or
contains only vertices mutually linked to v. The upper bound
does not even require v to be fresh to L. -/
theorem finiteDirectedCliqueCapacity_insert_le
    (E : Nat → Nat → Bool) (L : Finset Nat) (v : Nat) :
    finiteDirectedCliqueCapacity E (insert v L) ≤
      max (finiteDirectedCliqueCapacity E L)
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E L v)) := by
  classical
  unfold finiteDirectedCliqueCapacity
  apply Finset.sup_le
  intro s hs
  have hPieces := Finset.mem_filter.mp hs
  have hSub : s ⊆ insert v L :=
    Finset.mem_powerset.mp hPieces.1
  have hClique : IsDirectedCliqueOn E s := hPieces.2
  by_cases hv : v ∈ s
  · have hEraseSub :
        s.erase v ⊆ mutualLinkedNeighbours E L v := by
      intro x hx
      obtain ⟨hxNe, hxS⟩ := Finset.mem_erase.mp hx
      have hxL : x ∈ L := by
        rcases Finset.mem_insert.mp (hSub hxS) with hEq | hL
        · exact False.elim (hxNe hEq)
        · exact hL
      have hxv : E x v = true :=
        hClique x hxS v hv hxNe
      have hvx : E v x = true :=
        hClique v hv x hxS (Ne.symm hxNe)
      exact Finset.mem_filter.mpr ⟨hxL, hxv, hvx⟩
    have hEraseClique : IsDirectedCliqueOn E (s.erase v) := by
      intro x hx y hy hxy
      exact hClique x (Finset.mem_erase.mp hx).2
        y (Finset.mem_erase.mp hy).2 hxy
    have hCapacity :=
      directedClique_card_le_capacity E
        (mutualLinkedNeighbours E L v) (s.erase v)
        hEraseSub hEraseClique
    have hCard : s.card = (s.erase v).card + 1 := by
      rw [Finset.card_erase_of_mem hv]
      have hsPos : 0 < s.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hRight : 1 + finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E L v) ≤
        max (finiteDirectedCliqueCapacity E L)
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E L v)) := le_max_right _ _
    -- The outer supremum was unfolded above; normalize these hypotheses too.
    simp only [finiteDirectedCliqueCapacity] at hCapacity hRight
    omega
  · have hSubL : s ⊆ L := by
      intro x hx
      rcases Finset.mem_insert.mp (hSub hx) with hEq | hL
      · subst x
        exact False.elim (hv hx)
      · exact hL
    have hCapacity :=
      directedClique_card_le_capacity E L s hSubL hClique
    exact hCapacity.trans (le_max_left _ _)

/-- For a new vertex v outside L, every old mutual-neighbour clique
extends by v, proving the lower half of the EXACT update formula. -/
theorem finiteDirectedCliqueCapacity_succ_mutual_le_insert
    (E : Nat → Nat → Bool) (L : Finset Nat) (v : Nat)
    (hv : v ∉ L) :
    1 + finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E L v) ≤
    finiteDirectedCliqueCapacity E (insert v L) := by
  classical
  let M := mutualLinkedNeighbours E L v
  have hBase : 1 ≤ finiteDirectedCliqueCapacity E (insert v L) := by
    have hSingleton : IsDirectedCliqueOn E ({v} : Finset Nat) := by
      intro x hx y hy hxy
      have hEqX : x = v := Finset.mem_singleton.mp hx
      have hEqY : y = v := Finset.mem_singleton.mp hy
      exact False.elim (hxy (hEqX.trans hEqY.symm))
    have hS :=
      directedClique_card_le_capacity E (insert v L)
        ({v} : Finset Nat) (by simp) hSingleton
    simpa using hS
  have hSup : finiteDirectedCliqueCapacity E M ≤
      finiteDirectedCliqueCapacity E (insert v L) - 1 := by
    unfold finiteDirectedCliqueCapacity
    apply Finset.sup_le
    intro s hs
    have hPieces := Finset.mem_filter.mp hs
    have hSub : s ⊆ M :=
      Finset.mem_powerset.mp hPieces.1
    have hClique : IsDirectedCliqueOn E s := hPieces.2
    have hvNotS : v ∉ s := by
      intro hvS
      have hvM : v ∈ M := hSub hvS
      have hvL : v ∈ L := (Finset.mem_filter.mp hvM).1
      exact hv hvL
    have hInsertSub : insert v s ⊆ insert v L := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hEq | hxS
      · subst x
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mp (hSub hxS)).1
    have hInsertClique : IsDirectedCliqueOn E (insert v s) := by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxV | hxS
      · subst x
        rcases Finset.mem_insert.mp hy with hyV | hyS
        · exact False.elim (hxy hyV.symm)
        · exact (Finset.mem_filter.mp (hSub hyS)).2.2
      · rcases Finset.mem_insert.mp hy with hyV | hyS
        · subst y
          exact (Finset.mem_filter.mp (hSub hxS)).2.1
        · exact hClique x hxS y hyS hxy
    have hCard : (insert v s).card = s.card + 1 := by
      simp [hvNotS]
    have hBound := directedClique_card_le_capacity E
      (insert v L) (insert v s) hInsertSub hInsertClique
    -- Match the explicit finite supremum unfolded in this subgoal.
    simp only [finiteDirectedCliqueCapacity] at hBound
    omega
  dsimp [M] at hSup
  omega

/-- EXACT incremental recurrence for maximum directed-clique size
when one genuinely NEW original is added to a finite linked pool. -/
theorem finiteDirectedCliqueCapacity_insert_eq
    (E : Nat → Nat → Bool) (L : Finset Nat) (v : Nat)
    (hv : v ∉ L) :
    finiteDirectedCliqueCapacity E (insert v L) =
      max (finiteDirectedCliqueCapacity E L)
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E L v)) := by
  apply le_antisymm
  · exact finiteDirectedCliqueCapacity_insert_le E L v
  · apply max_le
    · exact finiteDirectedCliqueCapacity_mono E L (insert v L)
        (by intro x hx; exact Finset.mem_insert_of_mem hx)
    · exact finiteDirectedCliqueCapacity_succ_mutual_le_insert
        E L v hv

theorem finiteDirectedCliqueCapacity_empty
    (E : Nat → Nat → Bool) :
    finiteDirectedCliqueCapacity E ∅ = 0 := by
  simp [finiteDirectedCliqueCapacity]

/-- When v has no edge to old linked vertices, adding it does
not increase capacity once the old linked pool already contains
at least one vertex (capacity at least one). -/
theorem finiteDirectedCliqueCapacity_insert_no_growth
    (E : Nat → Nat → Bool) (L : Finset Nat) (v : Nat)
    (hv : v ∉ L)
    (hNo : ∀ x ∈ L, E x v = false)
    (hOldCap : 1 ≤ finiteDirectedCliqueCapacity E L) :
    finiteDirectedCliqueCapacity E (insert v L) =
      finiteDirectedCliqueCapacity E L := by
  have hEmpty : mutualLinkedNeighbours E L v = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxL, hxMutual⟩ := Finset.mem_filter.mp hx
      have hxEdge : E x v = true := hxMutual.1
      rw [hNo x hxL] at hxEdge
      cases hxEdge
    · simp
  rw [finiteDirectedCliqueCapacity_insert_eq E L v hv, hEmpty]
  rw [finiteDirectedCliqueCapacity_empty]
  simpa using (max_eq_left hOldCap :
    max (finiteDirectedCliqueCapacity E L) 1 =
      finiteDirectedCliqueCapacity E L)

/-- A budget for the precise next unreserved linked pool R ∪ L ∪ {v}.
There is no unjustified assertion that the next diary's live reserved
set or actual linked pool MUST be this one: that remains a geometric
hypothesis to verify for each proposed selected column. -/
theorem finitePoolCliqueCheck_false_of_one_new_link_budget
    (E : Nat → Nat → Bool) (q : Nat)
    (R L : Finset Nat) (v : Nat)
    (hv : v ∉ L)
    (hBudget : R.card +
      max (finiteDirectedCliqueCapacity E L)
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E L v)) < q) :
    finitePoolCliqueCheck E q (R ∪ insert v L) = false := by
  apply finitePoolCliqueCheck_false_of_reserved_plus_link_capacity
  rw [finiteDirectedCliqueCapacity_insert_eq E L v hv]
  exact hBudget

/-- Safe K4 real-old-table regression: old reserved 0 sees linked
selected originals 1,2,3, but 1,2,3 are mutually nonadjacent.
The clique capacity stays one as more linked originals arrive. -/
def k4ThreeIndependentLinks (i j : Nat) : Bool :=
  decide ((i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
          (j = 0 ∧ (i = 1 ∨ i = 2 ∨ i = 3)))

/-- Bad variation: make the newly linked selected original 3
mutually adjacent to old selected original 1. This raises
the linked capacity from one to two, creating a future K4. -/
def k4ThreeLinksNewEdge (i j : Nat) : Bool :=
  decide ((i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
          (j = 0 ∧ (i = 1 ∨ i = 2 ∨ i = 3)) ∨
          (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))

theorem k4LinkedCapacity_insert_no_growth_regression :
    finiteDirectedCliqueCapacity k4ThreeIndependentLinks
      ({1, 2} : Finset Nat) = 1 ∧
    finiteDirectedCliqueCapacity k4ThreeIndependentLinks
      (insert 3 ({1, 2} : Finset Nat)) = 1 ∧
    finiteNeighbourCliqueCheck k4ThreeIndependentLinks 4 3
      (fun i => decide (i < 4)) = false := by
  decide

theorem k4LinkedCapacity_insert_growth_regression :
    finiteDirectedCliqueCapacity k4ThreeLinksNewEdge
      ({1, 2} : Finset Nat) = 1 ∧
    finiteDirectedCliqueCapacity k4ThreeLinksNewEdge
      (mutualLinkedNeighbours k4ThreeLinksNewEdge
        ({1, 2} : Finset Nat) 3) = 1 ∧
    finiteDirectedCliqueCapacity k4ThreeLinksNewEdge
      (insert 3 ({1, 2} : Finset Nat)) = 2 ∧
    finiteNeighbourCliqueCheck k4ThreeLinksNewEdge 4 3
      (fun i => decide (i < 4)) = true := by
  decide

end Kk
