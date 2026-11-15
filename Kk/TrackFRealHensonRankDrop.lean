import Kk.ExactFiniteNeighbourRealization
import Kk.LinkedCliqueCapacityUpdate
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Track F: real Henson one-type rank drop and cofinal coding vertices

This module uses the actual old-vertex directed Boolean adjacency table,
the normalized forbidden-family semantics, and the explicitly stipulated
OnePointLeftDense property of the fixed Henson enumeration. No abstract
diary-to-BRD characterization or selected-front surrogate is assumed.

The English proof and hostile scope audit were committed before Lean in
docs/track_f_real_henson_rank_drop_english_audit.md.

This proves the ONE-coordinate physical rank-drop premise and cofinal
zero-padding. It does not prove joint multi-sort rank-largeness,
compatibility across arbitrary induced embeddings, finite deletion in
a tree of prefix nodes, or unavoidability of a prescribed diary.
-/

namespace Kk

/-- The actual one-type rank is ell-1 minus the largest directed old
neighbourhood clique. For a genuine K_ell-free one-point type, the
capacity is below ell-1; rank 0 is forbidden. Manuscript rank is
one-based, unlike the abstract RankLargeness rank. -/
def finiteHensonTypeRank
    (ell : Nat) (E : Nat → Nat → Bool) (U : Finset Nat) : Nat :=
  ell - 1 - finiteDirectedCliqueCapacity E U

/-- Enlarging the genuine old neighbourhood can only decrease the
one-type rank. This uses the FULL old graph, not a diary axiom. -/
theorem finiteHensonTypeRank_antitone
    (ell : Nat) (E : Nat → Nat → Bool)
    (U V : Finset Nat) (hUV : U ⊆ V) :
    finiteHensonTypeRank ell E V ≤
      finiteHensonTypeRank ell E U := by
  unfold finiteHensonTypeRank
  have hCap := finiteDirectedCliqueCapacity_mono E U V hUV
  omega

/-- A genuine K_ell-free type U over a complete initial segment has
coding representatives arbitrarily far in the ORIGINAL Henson order.
Every old and intervening edge column is exact in BOTH directions:
the only positive old bits are those in U. -/
theorem henson_leftDense_cofinal_exact_type
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front bound : Nat) (U : Finset Nat)
    (hBelow : ∀ x ∈ U, x < front)
    (hCapacity : finiteDirectedCliqueCapacity E U < ell - 1) :
    ∃ v : Nat, front ≤ v ∧ bound ≤ v ∧
      ∀ x : Nat, x < v →
        E x v = decide (x ∈ U) ∧
        E v x = decide (x ∈ U) := by
  have hBelowLater : ∀ x ∈ U, x < max front bound := by
    intro x hx
    exact lt_of_lt_of_le (hBelow x hx) (le_max_left _ _)
  have hSafe : finitePoolCliqueCheck E (ell - 1) U = false :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E (ell - 1) U).2
      hCapacity
  obtain ⟨v, hv, hColumn⟩ :=
    henson_leftDense_realizes_exact_finite_neighbour_set
      ell hell E hAvoid hDense (max front bound) U
      hBelowLater hSafe
  exact ⟨v, (le_max_left _ _).trans hv,
    (le_max_right _ _).trans hv, hColumn⟩

/-- A genuine positive-rank Henson one-type has a REAL extension
decreasing the rank by precisely one. Let C be an attained old
maximum clique. The new original v is adjacent to exactly C among
ALL earlier originals, including unused parameters and gaps. The
new old-neighbour set U∪{v} remains admissible (K_(ell-1)-free).

The condition cap(U)+3≤ell is exactly one-type rank≥2.
OnePointLeftDense is explicit; K_ell avoidance alone is insufficient. -/
theorem henson_leftDense_exact_type_rank_drop
    (ell : Nat) (hell : 3 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell (by omega) →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (front : Nat) (U : Finset Nat)
    (hBelow : ∀ x ∈ U, x < front)
    (hCapacity : finiteDirectedCliqueCapacity E U + 3 ≤ ell) :
    ∃ (C : Finset Nat) (v : Nat),
      C ⊆ U ∧ IsDirectedCliqueOn E C ∧
      C.card = finiteDirectedCliqueCapacity E U ∧
      front ≤ v ∧
      (∀ x : Nat, x < v →
        E x v = decide (x ∈ C) ∧
        E v x = decide (x ∈ C)) ∧
      finiteDirectedCliqueCapacity E (insert v U) =
        finiteDirectedCliqueCapacity E U + 1 ∧
      finitePoolCliqueCheck E (ell - 1) (insert v U) = false ∧
      finiteHensonTypeRank ell E (insert v U) + 1 =
        finiteHensonTypeRank ell E U := by
  classical
  obtain ⟨C, hCU, hClique, hCcard⟩ :=
    finiteDirectedCliqueCapacity_attained E U
  have hCBelow : ∀ x ∈ C, x < front := by
    intro x hx
    exact hBelow x (hCU hx)
  have hCSafe : finitePoolCliqueCheck E (ell - 1) C = false := by
    apply (finitePoolCliqueCheck_false_iff E (ell - 1) C).2
    rintro ⟨s, hs, hsCard, _⟩
    have hle : s.card ≤ C.card := Finset.card_le_card hs
    omega
  obtain ⟨v, hv, hColumn⟩ :=
    henson_leftDense_realizes_exact_finite_neighbour_set
      ell (by omega) E hAvoid hDense front C hCBelow hCSafe
  have hvNotU : v ∉ U := by
    intro hvU
    have hvlt := hBelow v hvU
    omega
  have hMutual : mutualLinkedNeighbours E U v = C := by
    ext x
    simp only [mutualLinkedNeighbours, Finset.mem_filter]
    constructor
    · rintro ⟨hxU, hxEdge, _⟩
      have hxlt : x < v := lt_of_lt_of_le (hBelow x hxU) hv
      rw [(hColumn x hxlt).1] at hxEdge
      simpa only [decide_eq_true_eq] using hxEdge
    · intro hxC
      have hxU : x ∈ U := hCU hxC
      have hxlt : x < v := lt_of_lt_of_le (hBelow x hxU) hv
      have hBits := hColumn x hxlt
      refine ⟨hxU, ?_, ?_⟩
      · simpa [hxC] using hBits.1
      · simpa [hxC] using hBits.2
  have hCapC : finiteDirectedCliqueCapacity E C =
      finiteDirectedCliqueCapacity E U := by
    apply Nat.le_antisymm
    · exact finiteDirectedCliqueCapacity_mono E C U hCU
    · calc
        finiteDirectedCliqueCapacity E U = C.card := hCcard.symm
        _ ≤ finiteDirectedCliqueCapacity E C :=
          directedClique_card_le_capacity E C C
            (Finset.Subset.refl _) hClique
  have hNewCap :
      finiteDirectedCliqueCapacity E (insert v U) =
        finiteDirectedCliqueCapacity E U + 1 := by
    rw [finiteDirectedCliqueCapacity_insert_eq E U v hvNotU,
      hMutual, hCapC]
    omega
  have hNewSafe :
      finitePoolCliqueCheck E (ell - 1) (insert v U) = false := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (insert v U)).2
    rw [hNewCap]
    omega
  have hNewRank :
      finiteHensonTypeRank ell E (insert v U) + 1 =
        finiteHensonTypeRank ell E U := by
    unfold finiteHensonTypeRank
    rw [hNewCap]
    omega
  exact ⟨C, v, hCU, hClique, hCcard, hv, hColumn,
    hNewCap, hNewSafe, hNewRank⟩

end Kk
