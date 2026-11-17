import Kk.TrackFActualCodingFibre
import Kk.TrackFRankLargeFiniteFan
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track F: safe positive-bit insertion in an ACTUAL Henson type

English-first proof and hostile audit:
docs/track_f_rank_three_triangle_english_audit.md

These elementary exact finite-clique-capacity lemmas are the
reusable graph-specific heart of the manuscript-rank-three
triangle richness construction. No published diary theorem
or Henson left-density hypothesis is assumed.

A genuine type extension with an additional positive old bit
is defined ONLY when the full actual K_(ell-1)-free old
neighbourhood certificate is supplied.
-/

namespace Kk

/-- Any one-vertex insertion into an ACTUAL finite directed
clique pool raises its maximum clique capacity by at most one,
without requiring symmetry or the new vertex to be fresh. -/
theorem finiteDirectedCliqueCapacity_insert_le_succ_actual
    (E : Nat → Nat → Bool) (P : Finset Nat) (v : Nat) :
    finiteDirectedCliqueCapacity E (insert v P) ≤
      finiteDirectedCliqueCapacity E P + 1 := by
  have hSub :
      mutualLinkedNeighbours E P v ⊆ P :=
    Finset.filter_subset _ _
  have hM :=
    finiteDirectedCliqueCapacity_mono E
      (mutualLinkedNeighbours E P v) P hSub
  have hInsert := finiteDirectedCliqueCapacity_insert_le E P v
  omega

/-- If all mutual old neighbours of the newly adjoined vertex
have clique capacity at most cap(P)-1, insertion preserves
the entire old clique capacity EXACTLY, provided v is fresh. -/
theorem finiteDirectedCliqueCapacity_insert_eq_of_safe_mutual
    (E : Nat → Nat → Bool) (P : Finset Nat) (v : Nat)
    (hv : v ∉ P)
    (hM : 1 + finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E P v) ≤
        finiteDirectedCliqueCapacity E P) :
    finiteDirectedCliqueCapacity E (insert v P) =
      finiteDirectedCliqueCapacity E P := by
  rw [finiteDirectedCliqueCapacity_insert_eq E P v hv]
  exact max_eq_left hM

end Kk

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- Add exactly one new positive bit at a fresh later original
level v. The COMPLETE finite actual old-neighbourhood test
must already be negative; no implicit age axiom is introduced. -/
def appendPositive (u : HensonOneType ell E) (v : Nat)
    (hu : u.level ≤ v)
    (hSafe : finitePoolCliqueCheck E (ell - 1)
      (insert v u.neighbours) = false) :
    HensonOneType ell E where
  level := v + 1
  neighbours := insert v u.neighbours
  below := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxv | hxU
    · omega
    · have hxOld := u.below x hxU
      omega
  safe := hSafe

/-- Full chronological extension of the original type under
one positive insertion, preserving all old *negative* bits. -/
theorem le_appendPositive
    (u : HensonOneType ell E) (v : Nat)
    (hu : u.level ≤ v)
    (hSafe : finitePoolCliqueCheck E (ell - 1)
      (insert v u.neighbours) = false) :
    u ≤ appendPositive u v hu hSafe := by
  constructor
  · change u.level ≤ v + 1
    omega
  · intro x hx
    change (x ∈ u.neighbours ↔ x ∈ insert v u.neighbours)
    constructor
    · intro hxU
      exact Finset.mem_insert_of_mem hxU
    · intro hxNew
      rcases Finset.mem_insert.mp hxNew with hxv | hxU
      · have hne : x ≠ v := by omega
        exact False.elim (hne hxv)
      · exact hxU

/-- Inserting one later actual original neighbour without
increasing actual clique capacity leaves the singleton
type's zero-based rank unchanged. -/
theorem rank_appendPositive_eq_of_capacity
    (u : HensonOneType ell E) (v : Nat)
    (hu : u.level ≤ v)
    (hSafe : finitePoolCliqueCheck E (ell - 1)
      (insert v u.neighbours) = false)
    (hCap : finiteDirectedCliqueCapacity E
      (insert v u.neighbours) =
        finiteDirectedCliqueCapacity E u.neighbours) :
    rank (appendPositive u v hu hSafe) = rank u := by
  unfold rank finiteHensonTypeRank
  change ell - 1 - finiteDirectedCliqueCapacity E
    (insert v u.neighbours) - 1 =
    ell - 1 - finiteDirectedCliqueCapacity E u.neighbours - 1
  rw [hCap]

end Kk.HensonOneType
