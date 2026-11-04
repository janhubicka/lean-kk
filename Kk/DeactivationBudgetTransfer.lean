import Kk.LivePoolFourQuadrants
import Mathlib.Tactic

/-!
# Capacity and complete-neighbourhood safety for deletion-only transitions

The English proof and hostile eight-point audit were committed FIRST in
`docs/deactivation_budget_transfer_english_audit.md` before this Lean source.

When BOTH sets of positive unreserved candidates and live reserved
witnesses shrink in ONE FIXED original-edge table, the actual directed
linked set shrinks. Thus the verified sufficient mixed clique-capacity
budget does not increase and a previously safe budget remains safe.

The stronger complete old-neighbourhood checker also transfers whenever
the NEXT complete finite positive-neighbour set is a subset of the OLD
one, even for different old/next original prefix cuts and columns.
These are precisely deletion-only transitions; no hidden claim that
the manuscript's prescribed canonical macrodiary has such transitions.

These results do NOT compare full parameter-closed corrected B3, assigned
upper L+ source types, or common labelled Kpt inverse-source orbits.
-/

namespace Kk

/-- All new directed links are old links if both positive-unreserved
candidates and live reserved witnesses SHRINK, in the fixed graph E. -/
theorem linkedOriginalsTo_mono
    (E : Nat → Nat → Bool)
    (U0 U1 R0 R1 : Finset Nat)
    (hU : U1 ⊆ U0) (hR : R1 ⊆ R0) :
    linkedOriginalsTo E U1 R1 ⊆ linkedOriginalsTo E U0 R0 := by
  intro x hx
  obtain ⟨hxU, y, hyR, hEdge⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hU hxU, y, hR hyR, hEdge⟩

/-- The sufficient old-reserved-cardinality plus linked-unreserved
CLIQUE CAPACITY budget is NONINCREASING under true deactivations.
No graph symmetry, K-freeness, or B3 assumption enters. -/
theorem linkedOriginals_deactivation_budget_le
    (E : Nat → Nat → Bool)
    (U0 U1 R0 R1 : Finset Nat)
    (hU : U1 ⊆ U0) (hR : R1 ⊆ R0) :
    R1.card + finiteDirectedCliqueCapacity E
      (linkedOriginalsTo E U1 R1) ≤
    R0.card + finiteDirectedCliqueCapacity E
      (linkedOriginalsTo E U0 R0) := by
  have hRCard := Finset.card_le_card hR
  have hCap := finiteDirectedCliqueCapacity_mono E
    (linkedOriginalsTo E U1 R1)
    (linkedOriginalsTo E U0 R0)
    (linkedOriginalsTo_mono E U0 U1 R0 R1 hU hR)
  omega

/-- A previously strict mixed pool clique-capacity budget
proves the NEW pool safe under a deletion-only live-set transition. -/
theorem finitePoolCliqueCheck_false_of_deactivation_budget
    (E : Nat → Nat → Bool) (q : Nat)
    (U0 U1 R0 R1 : Finset Nat)
    (hU : U1 ⊆ U0) (hR : R1 ⊆ R0)
    (hOldBudget : R0.card + finiteDirectedCliqueCapacity E
      (linkedOriginalsTo E U0 R0) < q) :
    finitePoolCliqueCheck E q
      (R1 ∪ linkedOriginalsTo E U1 R1) = false := by
  apply finitePoolCliqueCheck_false_of_reserved_plus_link_capacity
  have hLe :=
    linkedOriginals_deactivation_budget_le E U0 U1 R0 R1 hU hR
  omega

/-- More strongly, a complete negative neighbourhood certificate
transfers from an old column to a next column whenever the NEXT
complete finite positive-neighbour set is literally contained in
the OLD complete positive-neighbour set, even if prefix cuts differ. -/
theorem finiteNeighbourCliqueCheck_false_of_neighbour_subset
    (E : Nat → Nat → Bool) (N0 N1 q : Nat)
    (oldNeighbour newNeighbour : Nat → Bool)
    (hSubset : oldNeighbourSet N1 newNeighbour ⊆
      oldNeighbourSet N0 oldNeighbour)
    (hOld : finiteNeighbourCliqueCheck E N0 q oldNeighbour = false) :
    finiteNeighbourCliqueCheck E N1 q newNeighbour = false := by
  apply (finiteNeighbourCliqueCheck_false_iff E N1 q newNeighbour).2
  rintro ⟨s, hCard, hBound, hClique⟩
  have hBadOld : HasNeighbourCliqueBelow E N0 q oldNeighbour := by
    refine ⟨s, hCard, ?_, hClique⟩
    intro x hx
    have hInNext : x ∈ oldNeighbourSet N1 newNeighbour := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (hBound x hx).1,
        (hBound x hx).2⟩
    have hInOld := Finset.mem_filter.mp (hSubset hInNext)
    exact ⟨Finset.mem_range.mp hInOld.1, hInOld.2⟩
  exact
    ((finiteNeighbourCliqueCheck_false_iff E N0 q oldNeighbour).1
      hOld) hBadOld

/-- Chosen Henson complete-column left density turns a
deletion-only CERTIFIED passing column into an actual later original.
This does NOT assert that canonical diary events are deletion-only. -/
theorem henson_leftDense_realizes_deactivated_column
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (N0 N1 : Nat)
    (oldNeighbour newNeighbour : Nat → Bool)
    (hSubset : oldNeighbourSet N1 newNeighbour ⊆
      oldNeighbourSet N0 oldNeighbour)
    (hOld : finiteNeighbourCliqueCheck E N0 (ell-1)
      oldNeighbour = false) :
    ∃ v : Nat, N1 ≤ v ∧
      ∀ x, x < v →
        E x v = (if x < N1 then newNeighbour x else false) ∧
        E v x = (if x < N1 then newNeighbour x else false) := by
  have hNext := finiteNeighbourCliqueCheck_false_of_neighbour_subset
    E N0 N1 (ell-1) oldNeighbour newNeighbour hSubset hOld
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense N1 newNeighbour hNext

/-- A K4 full-positive neighbourhood triangle becomes safe after one
passing bit is removed. The converse of the subset safety theorem is
FALSE: an unsafe old column can become safe by deletion. -/
def k4OldTriangleEdge (i j : Nat) : Bool :=
  decide (i < 3 ∧ j < 3 ∧ i ≠ j)

theorem k4_neighbour_deactivation_rescues_forbidden_column :
    finiteNeighbourCliqueCheck k4OldTriangleEdge 3 3
      (fun i => decide (i < 3)) = true ∧
    finiteNeighbourCliqueCheck k4OldTriangleEdge 3 3
      (fun i => decide (i < 2)) = false := by
  decide

/-- Actual safe old reserved/selected star from PR #54:
deleting one old selected passing bit preserves complete safety. -/
theorem k4_safe_star_neighbour_deactivation :
    finiteNeighbourCliqueCheck k4OldLinksStarEdge 3 3
      (fun i => decide (i < 2)) = false := by
  have hSubset : oldNeighbourSet 3
      (fun i => decide (i < 2)) ⊆
      oldNeighbourSet 3 k4OldLinksNextNeighbour := by decide
  exact finiteNeighbourCliqueCheck_false_of_neighbour_subset
    k4OldLinksStarEdge 3 3 3 k4OldLinksNextNeighbour
    (fun i => decide (i < 2)) hSubset k4OldLinks_safe_by_capacity

end Kk
