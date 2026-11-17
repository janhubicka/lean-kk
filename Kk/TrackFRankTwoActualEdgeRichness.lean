import Kk.TrackFActualCodingFibre
import Kk.TrackFRankLargeFiniteFan
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track F: actual edge richness of a manuscript rank-two large fibre

The English proof and hostile audit were committed first:
docs/track_f_rank_two_rich_edge_english_audit.md

The theorem is about the ACTUAL ordinary graph E and the genuine
coding-node predicate IsCodingNode, not hypothetical diary nodes.
Lean rank 1 corresponds to manuscript singleton rank 2.

Every rank-one-large set consisting of actual coding nodes above a
rank-one Henson one-type contains TWO genuine later original vertices
joined by an actual edge in BOTH orientations.

The proof uses two rank-zero dense daughter cones with disjoint
fresh old-neighbourhood markers, the exact directed clique-capacity
insertion recurrence, and density of the second daughter. No
Henson left-density axiom or published big Ramsey degree is assumed.
This is ONLY the rank-two edge case, not rank-three triangle
richness or full multi-sort graph-age realization.
-/

namespace Kk.HensonOneType

variable {ell : Nat} {E : Nat → Nat → Bool}

/-- A rank-one-large set of ACTUAL coding nodes in a finite Henson
one-type tree contains an ACTUAL two-vertex clique. Both original
graph orientations are proved, and the source vertices are ordered.

The only hypotheses on the set S are recursive rank-one largeness
above u, and the EXACT actual coding-column predicate for its
members. This uses neither an assumed diary BRD theorem nor a
new axiom of Henson graph richness.

Rank 1 here is ZERO-BASED (manuscript rank 2). -/
theorem rank_one_large_actualCoding_contains_edge
    (S : Set (HensonOneType ell E))
    (u : HensonOneType ell E)
    (hu : rank u = 1)
    (hLarge : RankLargeness.Large rank S 1 u)
    (hActual : ∀ z : HensonOneType ell E,
      z ∈ S → IsCodingNode z) :
    ∃ x y : HensonOneType ell E,
      x ∈ S ∧ y ∈ S ∧ x.level < y.level ∧
      E x.level y.level = true ∧
      E y.level x.level = true := by
  classical
  have hEmpty : ∀ v ∈ (∅ : Finset (HensonOneType ell E)),
      u ≤ v ∧ rank v = 0 := by
    intro v hv
    simp at hv
  obtain ⟨a, hua, haRank, haLarge, _, _⟩ :=
    rank_large_fresh_daughter S 0 u hu hLarge
      (∅ : Finset (HensonOneType ell E)) hEmpty
  have hOne : ∀ v ∈ ({a} : Finset (HensonOneType ell E)),
      u ≤ v ∧ rank v = 0 := by
    intro v hv
    have hEq : v = a := Finset.mem_singleton.mp hv
    subst v
    exact ⟨hua, haRank⟩
  obtain ⟨b, hub, hbRank, hbLarge, _hNo, hMark⟩ :=
    rank_large_fresh_daughter S 0 u hu hLarge
      ({a} : Finset (HensonOneType ell E)) hOne
  have hFreshDisj :
      Disjoint (a.neighbours \ u.neighbours)
        (b.neighbours \ u.neighbours) :=
    hMark a (by simp)
  let H : Nat := max a.level b.level
  have haH : a.level ≤ H := le_max_left _ _
  have hbH : b.level ≤ H := le_max_right _ _
  let z : HensonOneType ell E := zeroPad a H haH
  have haz : a ≤ z := le_zeroPad a H haH
  obtain ⟨x, hzx, hxS⟩ := haLarge z haz
  have hxH : H ≤ x.level := hzx.1
  have hxCoding : IsCodingNode x := hActual x hxS
  have hUSafe :
      finiteDirectedCliqueCapacity E u.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) u.neighbours).1 u.safe
  have hBSafe :
      finiteDirectedCliqueCapacity E b.neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) b.neighbours).1 b.safe
  have hUCap : finiteDirectedCliqueCapacity E u.neighbours + 3 = ell := by
    dsimp [rank, finiteHensonTypeRank] at hu
    omega
  have hBCap : finiteDirectedCliqueCapacity E b.neighbours + 2 = ell := by
    dsimp [rank, finiteHensonTypeRank] at hbRank
    omega
  have hMutualSub :
      mutualLinkedNeighbours E b.neighbours x.level ⊆ u.neighbours := by
    intro c hc
    by_contra hcNotU
    have hcB : c ∈ b.neighbours :=
      (Finset.mem_filter.mp hc).1
    have hcFreshB : c ∈ b.neighbours \ u.neighbours :=
      Finset.mem_sdiff.mpr ⟨hcB, hcNotU⟩
    have hcH : c < H :=
      lt_of_lt_of_le (b.below c hcB) hbH
    have hcX : c < x.level := lt_of_lt_of_le hcH hxH
    have hBit : E c x.level = true :=
      (Finset.mem_filter.mp hc).2.1
    have hcInX : c ∈ x.neighbours := by
      have hOldBit := (hxCoding c hcX).1
      have hDecision : decide (c ∈ x.neighbours) = true :=
        hOldBit.symm.trans hBit
      simpa only [decide_eq_true_eq] using hDecision
    have hcInA : c ∈ a.neighbours := by
      have hPad : c ∈ z.neighbours :=
        (hzx.2 c hcH).mpr hcInX
      exact hPad
    have hcFreshA : c ∈ a.neighbours \ u.neighbours :=
      Finset.mem_sdiff.mpr ⟨hcInA, hcNotU⟩
    exact (Finset.disjoint_left.mp hFreshDisj)
      hcFreshA hcFreshB
  have hxNotB : x.level ∉ b.neighbours := by
    intro hxB
    have hLt := b.below x.level hxB
    omega
  have hCapMutual :
      finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E b.neighbours x.level) ≤
      finiteDirectedCliqueCapacity E u.neighbours :=
    finiteDirectedCliqueCapacity_mono E
      (mutualLinkedNeighbours E b.neighbours x.level)
      u.neighbours hMutualSub
  have hCapNew :
      finiteDirectedCliqueCapacity E
        (insert x.level b.neighbours) ≤
      finiteDirectedCliqueCapacity E b.neighbours := by
    rw [finiteDirectedCliqueCapacity_insert_eq
      E b.neighbours x.level hxNotB]
    omega
  have hSafeNew :
      finitePoolCliqueCheck E (ell - 1)
        (insert x.level b.neighbours) = false := by
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E (ell - 1) (insert x.level b.neighbours)).2
    omega
  let t : HensonOneType ell E := {
    level := x.level + 1
    neighbours := insert x.level b.neighbours
    below := by
      intro c hc
      rcases Finset.mem_insert.mp hc with hcEq | hcB
      · omega
      · have hcOld := b.below c hcB
        omega
    safe := hSafeNew
  }
  have hbt : b ≤ t := by
    refine ⟨by dsimp [t]; omega, ?_⟩
    intro c hc
    change (c ∈ b.neighbours ↔ c ∈ insert x.level b.neighbours)
    constructor
    · intro hcB
      exact Finset.mem_insert_of_mem hcB
    · intro hcNew
      rcases Finset.mem_insert.mp hcNew with hcEq | hcB
      · have hne : c ≠ x.level := by omega
        exact False.elim (hne hcEq)
      · exact hcB
  obtain ⟨y, hty, hyS⟩ := hbLarge t hbt
  have hyCoding : IsCodingNode y := hActual y hyS
  have hxy : x.level < y.level := by
    have hL : x.level + 1 ≤ y.level := hty.1
    omega
  have hxInY : x.level ∈ y.neighbours := by
    have hxInT : x.level ∈ t.neighbours := by
      change x.level ∈ insert x.level b.neighbours
      exact Finset.mem_insert_self _ _
    have hxLtT : x.level < t.level := by
      dsimp [t]
      omega
    exact (hty.2 x.level hxLtT).mp hxInT
  have hActualEdge := hyCoding x.level hxy
  have hForward : E x.level y.level = true := by
    simpa [hxInY] using hActualEdge.1
  have hBackward : E y.level x.level = true := by
    simpa [hxInY] using hActualEdge.2
  exact ⟨x, y, hxS, hyS, hxy, hForward, hBackward⟩

end Kk.HensonOneType
