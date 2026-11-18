import Kk.TrackFPrivateRankZeroDescendants
import Kk.TrackFCollapseCliqueFeasibility
import Mathlib.Tactic

/-!
# Track F: actual raw clique ages on private rank-zero source descendants

Proof and adversarial audit before Lean:
docs/track_f_private_raw_transfer_english_audit.md

The parent map is arbitrary and need not be injective. Mixed supports
are measured in PRIVATE indices; they may collapse to a singleton
support of original source sorts. This module does not assert any
diary lower bound or target multi-sort compatibility.
-/

namespace Kk

/-- The literal full neighbourhood of an extension is the old
neighbourhood together with exactly the fresh positive markers.
The proof needs exact old positive AND negative prefix bits. -/
theorem trackFPrivate_neighbours_union_fresh
    {ell : Nat} {E : Nat → Nat → Bool}
    (u v : HensonOneType ell E) (huv : u ≤ v) :
    v.neighbours =
      u.neighbours ∪ (v.neighbours \ u.neighbours) := by
  classical
  have hSub : u.neighbours ⊆ v.neighbours := by
    intro x hx
    exact (huv.2 x (u.below x hx)).mp hx
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hx
    by_cases hOld : x ∈ u.neighbours
    · exact Or.inl hOld
    · exact Or.inr ⟨hx, hOld⟩
  · rintro (hx | ⟨hx, _⟩)
    · exact hSub hx
    · exact hx

/-- Every genuine Henson one-type has positive literal singleton
raw age, including at rank zero. This follows directly from its
K_(ell-1)-free safety certificate, not from rank subtraction. -/
theorem trackFPrivate_singleton_raw_positive
    {ell : Nat} {E : Nat → Nat → Bool}
    (d H : Nat) (g : Fin d → HensonOneType ell E)
    (hLevel : ∀ i, (g i).level = H) (i : Fin d) :
    1 ≤ trackFCommonRawAge d ell H E
      (fun j => (g j).neighbours) {i} := by
  have hBelow : ∀ j x, x ∈ (g j).neighbours → x < H := by
    intro j x hx
    have hxLt := (g j).below x hx
    simpa only [hLevel j] using hxLt
  have hPool :=
    trackFCommonNeighbourPool_singleton d H
      (fun j => (g j).neighbours) hBelow i
  have hSafe :
      finiteDirectedCliqueCapacity E (g i).neighbours < ell - 1 :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E
      (ell - 1) (g i).neighbours).mp (g i).safe
  unfold trackFCommonRawAge
  rw [hPool]
  omega

/-- For ANY finite collection of (possibly repeated) actual Henson
source fibres, obtain a common level of rank-zero dense private
daughters. Every support of at least TWO private indices has exactly
the original raw clique age on its parent image, while every private
singleton raw age is at least one.

This is the missing full physical raw-feasibility bridge from
the private descendant selection theorem to rank-zero finite
labelled graph realization. No injectivity of pi, uniform rank,
left-density, diary theorem or BRD claim is presumed. -/
theorem trackFPrivate_rank_zero_raw_transfer
    (p d ell m : Nat) (E : Nat → Nat → Bool)
    (u : Fin p → HensonOneType ell E)
    (S : Fin p → Set (HensonOneType ell E))
    (π : Fin d → Fin p)
    (hRootLevel : ∀ a, (u a).level = m)
    (hLarge : ∀ a, RankLargeness.Large HensonOneType.rank
      (S a) (HensonOneType.rank (u a)) (u a)) :
    ∃ H : Nat, ∃ g : Fin d → HensonOneType ell E,
      (∀ i : Fin d, (g i).level = H ∧
        u (π i) ≤ g i ∧ HensonOneType.rank (g i) = 0 ∧
        RankLargeness.Large HensonOneType.rank
          (S (π i)) 0 (g i)) ∧
      (∀ Q : Finset (Fin d), 2 ≤ Q.card →
        trackFCommonRawAge d ell H E
          (fun i => (g i).neighbours) Q =
        trackFCommonRawAge p ell m E
          (fun a => (u a).neighbours) (Q.image π)) ∧
      (∀ i : Fin d, 1 ≤
        trackFCommonRawAge d ell H E
          (fun j => (g j).neighbours) {i}) := by
  classical
  let roots : Fin d → HensonOneType ell E := fun i => u (π i)
  let fibres : Fin d → Set (HensonOneType ell E) :=
    fun i => S (π i)
  have hReq : ∀ i : Fin d,
      RankLargeness.Large HensonOneType.rank
        (fibres i) (HensonOneType.rank (roots i)) (roots i) :=
    fun i => hLarge (π i)
  obtain ⟨H, g, hValid, hCross⟩ :=
    HensonOneType.rank_large_private_rank_zero_common_front
      d roots fibres hReq
  let oldU : Fin p → Finset Nat := fun a => (u a).neighbours
  let fresh : Fin d → Finset Nat :=
    fun i => (g i).neighbours \ (u (π i)).neighbours
  have hOld : ∀ a x, x ∈ oldU a → x < m := by
    intro a x hx
    have hlt := (u a).below x hx
    simpa only [hRootLevel a] using hlt
  have hNew : ∀ i x, x ∈ fresh i → m ≤ x ∧ x < H := by
    intro i x hx
    have hxG : x ∈ (g i).neighbours :=
      (Finset.mem_sdiff.mp hx).1
    have hxNotOld : x ∉ (u (π i)).neighbours :=
      (Finset.mem_sdiff.mp hx).2
    have hiExt : u (π i) ≤ g i := (hValid i).2.1
    have hxLow : m ≤ x := by
      by_contra hNot
      have hxLt : x < m := by omega
      have hxLtRoot : x < (u (π i)).level := by
        simpa only [hRootLevel (π i)] using hxLt
      have hxOld : x ∈ (u (π i)).neighbours :=
        (hiExt.2 x hxLtRoot).mpr hxG
      exact hxNotOld hxOld
    have hxHigh : x < H := by
      have hxLt := (g i).below x hxG
      simpa only [(hValid i).1] using hxLt
    exact ⟨hxLow, hxHigh⟩
  have hDisjoint : ∀ i j : Fin d, i ≠ j →
      Disjoint (fresh i) (fresh j) :=
    fun i j hij => hCross i j hij
  have hNeighbourEq :
      (fun i : Fin d => (g i).neighbours) =
        trackFAddDisjointMarkers d (fun i => oldU (π i)) fresh := by
    funext i
    change (g i).neighbours =
      (u (π i)).neighbours ∪
        ((g i).neighbours \ (u (π i)).neighbours)
    exact trackFPrivate_neighbours_union_fresh
      (u (π i)) (g i) (hValid i).2.1
  refine ⟨H, g, (by intro i; exact hValid i), ?_, ?_⟩
  · intro Q hTwoCard
    have hNonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hNonempty
    have hTwo : ∃ a ∈ Q, ∃ b ∈ Q, a ≠ b := by
      by_contra hNo
      have hSubset : Q ⊆ {i} := by
        intro j hj
        have hji : j = i := by
          by_contra hNe
          exact hNo ⟨j, hj, i, hi, hNe⟩
        simpa [hji]
      have hLe : Q.card ≤ 1 := by
        calc
          Q.card ≤ ({i} : Finset (Fin d)).card :=
            Finset.card_le_card hSubset
          _ = 1 := by simp
      omega
    have hmH : m ≤ H := by
      have hExt : (u (π i)).level ≤ (g i).level :=
        ((hValid i).2.1).1
      simpa only [hRootLevel (π i), (hValid i).1] using hExt
    rw [hNeighbourEq]
    exact trackFCommonRawAge_disjoint_collapse
      d p ell m H hmH E π oldU fresh
      (fun i x hx => hOld (π i) x hx) hNew hDisjoint Q hTwo
  · intro i
    exact trackFPrivate_singleton_raw_positive
      d H g (fun j => (hValid j).1) i

end Kk
