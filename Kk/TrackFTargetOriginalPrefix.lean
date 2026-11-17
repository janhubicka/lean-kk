import Kk.TrackFActualCodingFibre
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Track F: a genuine target Henson prefix type from an actual original

English proof / hostile audit committed first:
docs/track_f_target_original_prefix_english_audit.md

If y is an ACTUAL target original after finite prefix H, its full
two-directed old adjacency column is an admissible Henson one-type.
The necessary finite K_(ell-1)-free neighbourhood certificate is
derived from the verified normalized forbidden family, not assumed.

This turns a target-prefix bit-vector coming from an actual original
into a true target one-type, but does NOT prove its rank matches a
source type or that the corresponding non-root source fibre is large.
-/

namespace Kk.HensonOneType

/-- Exactly the old target neighbours of ACTUAL original y
among indices below H, in the forward graph-edge orientation. -/
def targetOldNeighbours (E : Nat → Nat → Bool)
    (H y : Nat) : Finset Nat :=
  (Finset.range H).filter (fun x => E x y = true)

/-- K_ell-freeness of the actual Henson graph forces the complete
old neighbour set of any later original y to be K_(ell-1)-free.
The reverse edge direction follows from normalized Henson symmetry.

No OnePointLeftDense condition is needed on the TARGET graph:
the target original y is already given. -/
theorem targetOldNeighbours_safe
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (H y : Nat) (hy : H ≤ y) :
    finitePoolCliqueCheck E (ell - 1)
      (targetOldNeighbours E H y) = false := by
  classical
  have hSym : ∀ x z : Nat, E x z = E z x :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  have hFree : ¬ HasCliqueBelow E (y + 1) ell :=
    hensonForbiddenFamily_no_prefix_cliques
      ell hell E hAvoid (y + 1)
  apply (finitePoolCliqueCheck_false_iff
    E (ell - 1) (targetOldNeighbours E H y)).2
  rintro ⟨s, hsP, hsCard, hsClique⟩
  have hsOld : ∀ x ∈ s, x < H := by
    intro x hx
    exact Finset.mem_range.mp
      (Finset.mem_filter.mp (hsP hx)).1
  have hsJoin : ∀ x ∈ s, E x y = true := by
    intro x hx
    exact (Finset.mem_filter.mp (hsP hx)).2
  have hyNot : y ∉ s := by
    intro hys
    have hxy := hsOld y hys
    omega
  have hCard : (insert y s).card = ell := by
    have hInsert : (insert y s).card = s.card + 1 := by
      simp [hyNot]
    omega
  have hBound : ∀ x ∈ insert y s, x < y + 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxy | hxS
    · omega
    · have hxH := hsOld x hxS
      omega
  have hClique : IsDirectedCliqueOn E (insert y s) := by
    intro x hx z hz hxz
    rcases Finset.mem_insert.mp hx with hxy | hxS
    · subst x
      rcases Finset.mem_insert.mp hz with hzy | hzS
      · exact False.elim (hxz hzy.symm)
      · exact (hSym y z).trans (hsJoin z hzS)
    · rcases Finset.mem_insert.mp hz with hzy | hzS
      · subst z
        exact hsJoin x hxS
      · exact hsClique x hxS z hzS hxz
  exact hFree ⟨insert y s, hCard, hBound, hClique⟩

/-- The actual target finite prefix of any later original is a
genuine consistent Henson one-type. It is constructed from the
REAL edge table and its exact verified forbidden-family avoidance. -/
def targetTypeOfOriginal
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (H y : Nat) (hy : H ≤ y) : HensonOneType ell E where
  level := H
  neighbours := targetOldNeighbours E H y
  below := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  safe := targetOldNeighbours_safe ell hell E hAvoid H y hy

/-- The constructed target type agrees with BOTH directed actual
old adjacency columns of its later original y on all indices <H.
It does not assume E symmetric without proof: symmetry follows
from the normalized Henson forbidden-family condition. -/
theorem targetTypeOfOriginal_columns
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (H y : Nat) (hy : H ≤ y) :
    ∀ x : Nat, x < H →
      E x y = decide (x ∈
        (targetTypeOfOriginal ell hell E hAvoid H y hy).neighbours) ∧
      E y x = decide (x ∈
        (targetTypeOfOriginal ell hell E hAvoid H y hy).neighbours) := by
  intro x hx
  have hSym : E y x = E x y :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid y x
  have hDecide :
      decide (x ∈ targetOldNeighbours E H y) = E x y := by
    cases h : E x y <;>
      simp [targetOldNeighbours, Finset.mem_filter,
        Finset.mem_range, hx, h]
  change E x y = decide (x ∈ targetOldNeighbours E H y) ∧
    E y x = decide (x ∈ targetOldNeighbours E H y)
  exact ⟨hDecide.symm, hSym.trans hDecide.symm⟩

end Kk.HensonOneType
