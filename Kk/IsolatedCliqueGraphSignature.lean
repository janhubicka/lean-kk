import Kk.IsolatedCliqueBlocks
import Mathlib.Tactic

/-!
# The full undirected graph signature of an isolated reserved block

K_ell-freeness of a directed Boolean edge table by itself is NOT
the full Henson-language condition: the normalized forbidden
family also excludes positive loops and asymmetric pairs.

The previously checked isolated-block insertion uses the genuine
symmetric onePointGraphEdge, so it should preserve symmetry
and irreflexivity. We prove these separately for each step and for
the entire appended block, then combine them with K_ell-freeness.

Every conclusion is about the actual edge table. It does not
construct the selected diary, prove the fixed-enumeration left-density
hypothesis or settle full parameter-closed corrected B3.
-/

namespace Kk

/-- Appending a genuine undirected one-point vertex to a symmetric
Boolean table preserves BOTH directions of every binary atom. -/
theorem onePointGraphEdge_symmetric_of_base
    (E : Nat → Nat → Bool) (N : Nat)
    (neighbour : Nat → Bool)
    (hSym : ∀ x y, E x y = E y x) :
    ∀ x y,
      onePointGraphEdge E N neighbour x y =
        onePointGraphEdge E N neighbour y x := by
  intro x y
  by_cases hx : x = N
  · subst x
    by_cases hy : y = N
    · subst y
      rfl
    · by_cases hylt : y < N
      · simp [onePointGraphEdge, hy, hylt]
      · simp [onePointGraphEdge, hy, hylt]
  · by_cases hy : y = N
    · subst y
      by_cases hxlt : x < N
      · simp [onePointGraphEdge, hx, hxlt]
      · simp [onePointGraphEdge, hx, hxlt]
    · simpa [onePointGraphEdge, hx, hy] using hSym x y

/-- A one-point extension gives the new vertex a false diagonal
and retains all old false diagonal values. -/
theorem onePointGraphEdge_irreflexive_of_base
    (E : Nat → Nat → Bool) (N : Nat)
    (neighbour : Nat → Bool)
    (hLoops : ∀ x, E x x = false) :
    ∀ x, onePointGraphEdge E N neighbour x x = false := by
  intro x
  by_cases hx : x = N
  · subst x
    simp [onePointGraphEdge]
  · simpa [onePointGraphEdge, hx] using hLoops x

/-- The complete iterated reserved-block table remains symmetric if
the original graph is symmetric. -/
theorem appendIsolatedCliqueBlock_symmetric
    (E : Nat → Nat → Bool) (N : Nat)
    (hSym : ∀ x y, E x y = E y x) :
    ∀ r x y,
      appendIsolatedCliqueBlock E N r x y =
        appendIsolatedCliqueBlock E N r y x := by
  intro r
  induction r with
  | zero =>
    intro x y
    exact hSym x y
  | succ r ih =>
    intro x y
    change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
      (N+r) (fun u => decide (N ≤ u ∧ u < N+r)) x y =
      onePointGraphEdge (appendIsolatedCliqueBlock E N r)
        (N+r) (fun u => decide (N ≤ u ∧ u < N+r)) y x
    exact onePointGraphEdge_symmetric_of_base
      (appendIsolatedCliqueBlock E N r) (N+r)
      (fun u => decide (N ≤ u ∧ u < N+r)) ih x y

/-- No positive diagonal is introduced at any reserved-block step. -/
theorem appendIsolatedCliqueBlock_irreflexive
    (E : Nat → Nat → Bool) (N : Nat)
    (hLoops : ∀ x, E x x = false) :
    ∀ r x, appendIsolatedCliqueBlock E N r x x = false := by
  intro r
  induction r with
  | zero =>
    intro x
    exact hLoops x
  | succ r ih =>
    intro x
    change onePointGraphEdge (appendIsolatedCliqueBlock E N r)
      (N+r) (fun u => decide (N ≤ u ∧ u < N+r)) x x = false
    exact onePointGraphEdge_irreflexive_of_base
      (appendIsolatedCliqueBlock E N r) (N+r)
      (fun u => decide (N ≤ u ∧ u < N+r)) ih x

/-- In a symmetric original graph, both directed mixed atoms from
every old original/parameter to a newly reserved block vertex are
absent, not merely the old-to-new orientation. -/
theorem appendIsolatedCliqueBlock_old_new_both_nonedges
    (E : Nat → Nat → Bool) (N r x j : Nat)
    (hSym : ∀ u v, E u v = E v u)
    (hx : x < N) (hj : j < r) :
    appendIsolatedCliqueBlock E N r x (N+j) = false ∧
      appendIsolatedCliqueBlock E N r (N+j) x = false := by
  have hForward :=
    appendIsolatedCliqueBlock_old_new_nonedge E N r x j hx hj
  have hReverse :=
    appendIsolatedCliqueBlock_symmetric E N hSym r (N+j) x
  exact ⟨hForward, hReverse.trans hForward⟩

/-- The actual finite isolated block is an undirected irreflexive
K_ell-free graph extension, not just a directed-clique-free table.
The K_ell condition applies to the entire old+new initial prefix. -/
theorem appendIsolatedCliqueBlock_graph_valid_prefix
    (E : Nat → Nat → Bool) (N ell r : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false)
    (hOld : ¬ HasCliqueBelow E N ell)
    (hR : r < ell) :
    (∀ x y,
      appendIsolatedCliqueBlock E N r x y =
        appendIsolatedCliqueBlock E N r y x) ∧
    (∀ x, appendIsolatedCliqueBlock E N r x x = false) ∧
    ¬ HasCliqueBelow (appendIsolatedCliqueBlock E N r)
      (N+r) ell := by
  exact ⟨appendIsolatedCliqueBlock_symmetric E N hSym r,
    appendIsolatedCliqueBlock_irreflexive E N hLoops r,
    appendIsolatedCliqueBlock_cliqueFree E N ell hEll hOld r hR⟩

end Kk
