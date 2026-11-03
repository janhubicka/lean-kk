import Kk.NeighbourhoodCardinality
import Mathlib.Tactic

/-!
# Safe insertion of an isolated reserved clique block

A resolved-copy construction wants to reserve r vertices forming a
clique. The easiest part of the geometric construction is to insert
these reserved originals consecutively, with edges to exactly the
earlier vertices of THIS block and no edges to any previously
existing original, selected vertex, or split/coding parameter.

This module constructs those finite edge tables by successive genuine
one-point extensions, proves the entire intermediate prefix remains
K_ell-free whenever r < ell, and proves that the old prefix is
preserved and the new vertices really form a clique.

It does NOT prove that all later selected vertices can be made
adjacent to the reserved block while respecting their other
parameters. Those later mixed-neighbourhood certificates remain
open and must be checked using the complete old adjacency table.
-/

namespace Kk

/-- Append an isolated r-clique above the old prefix [0,N). Each
new vertex N+a is adjacent to exactly the earlier block vertices
in [N,N+a); all old-to-new edges are absent. -/
def appendIsolatedCliqueBlock
    (E : Nat → Nat → Bool) (N : Nat) (r : Nat) :
    Nat → Nat → Bool :=
  Nat.rec E
    (fun a old =>
      onePointGraphEdge old (N+a)
        (fun x => decide (N ≤ x ∧ x < N+a))) r

/-- Appending reserved originals never changes any original-old
edge or nonedge in the prefix below N. -/
theorem appendIsolatedCliqueBlock_old
    (E : Nat → Nat → Bool) (N : Nat) :
    ∀ r x y, x < N → y < N →
      appendIsolatedCliqueBlock E N r x y = E x y := by
  intro r
  induction r with
  | zero =>
    intro x y hx hy
    rfl
  | succ r ih =>
    intro x y hx hy
    change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
      (N+r) (fun u => decide (N ≤ u ∧ u < N+r)) x y = E x y
    rw [onePointGraphEdge_old
      (appendIsolatedCliqueBlock E N r) (N+r)
      (fun u => decide (N ≤ u ∧ u < N+r))
      x y (by omega) (by omega)]
    exact ih x y hx hy

/-- Every new block vertex is completely nonadjacent to every
earlier original, including all prior selected/coding parameters. -/
theorem appendIsolatedCliqueBlock_old_new_nonedge
    (E : Nat → Nat → Bool) (N : Nat) :
    ∀ r x j, x < N → j < r →
      appendIsolatedCliqueBlock E N r x (N+j) = false := by
  intro r
  induction r with
  | zero =>
    intro x j hx hj
    omega
  | succ r ih =>
    intro x j hx hj
    by_cases hjr : j = r
    · subst j
      change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
        (N+r) (fun u => decide (N ≤ u ∧ u < N+r))
        x (N+r) = false
      rw [onePointGraphEdge_right
        (appendIsolatedCliqueBlock E N r) (N+r)
        (fun u => decide (N ≤ u ∧ u < N+r)) x (by omega)]
      simp [show ¬ N ≤ x by omega]
    · have hjLt : j < r := by omega
      change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
        (N+r) (fun u => decide (N ≤ u ∧ u < N+r))
        x (N+j) = false
      rw [onePointGraphEdge_old
        (appendIsolatedCliqueBlock E N r) (N+r)
        (fun u => decide (N ≤ u ∧ u < N+r))
        x (N+j) (by omega) (by omega)]
      exact ih x j hx hjLt

/-- Each pair of distinct appended vertices has the prescribed
positive directed edge. The block is an actual clique, not just a
collection of anonymous capacity constraints. -/
theorem appendIsolatedCliqueBlock_new_clique
    (E : Nat → Nat → Bool) (N : Nat) :
    ∀ r i j, i < r → j < r → i ≠ j →
      appendIsolatedCliqueBlock E N r (N+i) (N+j) = true := by
  intro r
  induction r with
  | zero =>
    intro i j hi hj hij
    omega
  | succ r ih =>
    intro i j hi hj hij
    by_cases hir : i = r
    · subst i
      have hjLt : j < r := by omega
      change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
        (N+r) (fun u => decide (N ≤ u ∧ u < N+r))
        (N+r) (N+j) = true
      rw [onePointGraphEdge_left
        (appendIsolatedCliqueBlock E N r) (N+r)
        (fun u => decide (N ≤ u ∧ u < N+r))
        (N+j) (by omega)]
      simp [show N ≤ N+j by omega, show N+j < N+r by omega]
    · have hiLt : i < r := by omega
      by_cases hjr : j = r
      · subst j
        change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
          (N+r) (fun u => decide (N ≤ u ∧ u < N+r))
          (N+i) (N+r) = true
        rw [onePointGraphEdge_right
          (appendIsolatedCliqueBlock E N r) (N+r)
          (fun u => decide (N ≤ u ∧ u < N+r))
          (N+i) (by omega)]
        simp [show N ≤ N+i by omega, show N+i < N+r by omega]
      · have hjLt : j < r := by omega
        change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
          (N+r) (fun u => decide (N ≤ u ∧ u < N+r))
          (N+i) (N+j) = true
        rw [onePointGraphEdge_old
          (appendIsolatedCliqueBlock E N r) (N+r)
          (fun u => decide (N ≤ u ∧ u < N+r))
          (N+i) (N+j) (by omega) (by omega)]
        exact ih i j hiLt hjLt hij

/-- The full set of old neighbours of the next reserved original
N+a is included in precisely a earlier vertices of its own block. -/
theorem appendIsolatedCliqueBlock_next_neighbour_card
    (N a : Nat) :
    (oldNeighbourSet (N+a)
      (fun x => decide (N ≤ x ∧ x < N+a))).card ≤ a := by
  have hSub :
      oldNeighbourSet (N+a)
          (fun x => decide (N ≤ x ∧ x < N+a))
        ⊆ Finset.Ico N (N+a) := by
    intro x hx
    have hFlag : decide (N ≤ x ∧ x < N+a) = true :=
      (Finset.mem_filter.mp hx).2
    have hRange : N ≤ x ∧ x < N+a := by
      simpa only [decide_eq_true_eq] using hFlag
    exact Finset.mem_Ico.mpr hRange
  have hCount := Finset.card_le_card hSub
  have hIco : (Finset.Ico N (N+a)).card = a := by simp
  omega

/-- Inserting a block of size strictly less than ell keeps EVERY
intermediate prefix K_ell-free, regardless of the old adjacency
table outside the prefix. This closes the auxiliary-block insertion
step without checking only selected graph-age shadows. -/
theorem appendIsolatedCliqueBlock_cliqueFree
    (E : Nat → Nat → Bool) (N ell : Nat)
    (hEll : 0 < ell)
    (hOld : ¬ HasCliqueBelow E N ell) :
    ∀ r, r < ell →
      ¬ HasCliqueBelow (appendIsolatedCliqueBlock E N r)
        (N+r) ell := by
  intro r
  induction r with
  | zero =>
    intro _
    simpa [appendIsolatedCliqueBlock] using hOld
  | succ r ih =>
    intro hR
    have hPrev := ih (by omega)
    have hCount :=
      appendIsolatedCliqueBlock_next_neighbour_card N r
    have hSmall :
        (oldNeighbourSet (N+r)
          (fun x => decide (N ≤ x ∧ x < N+r))).card < ell-1 := by
      omega
    have hSafe := onePointGraph_safe_of_small_neighbour_set
      (appendIsolatedCliqueBlock E N r) (N+r) ell
      (fun x => decide (N ≤ x ∧ x < N+r))
      hEll hPrev hSmall
    change ¬ HasCliqueBelow
      (onePointGraphEdge (appendIsolatedCliqueBlock E N r)
        (N+r) (fun x => decide (N ≤ x ∧ x < N+r)))
      (N+(r+1)) ell
    simpa only [Nat.add_succ] using hSafe

end Kk
