import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Exact finite continuation tests for an isolated reserved block

The English proof and adversarial audit were committed FIRST in
docs/isolated_block_continuation_age_english_audit.md.

All statements use the existing finite directed-clique predicate,
Boolean clique checker, and exact finite clique capacity. The table E
here is ordinary graph adjacency, corresponding to the graph L.binary
bit in a numerical-H application; it is NOT the auxiliary Kpt E field.

An exact join-capacity calculation separates the old-plus-future
continuation test from the inserted block's concrete clique bound.
The reserved pool need not itself be a clique. Internal future edges
remain arbitrary, and every gap-to-future zero must be supplied.

This module does not construct simultaneous marked columns, compute
numerical-H generation capacities, identify an integer graph-age
canonicalizer, or construct a global resolved copy.
-/

namespace Kk

/-- The actual finite clique capacity is attained by a concrete clique
subset. The empty clique makes this valid even for an empty pool. -/
theorem finiteDirectedCliqueCapacity_attained
    (E : Nat → Nat → Bool) (P : Finset Nat) :
    ∃ s : Finset Nat,
      s ⊆ P ∧
      IsDirectedCliqueOn E s ∧
      s.card = finiteDirectedCliqueCapacity E P := by
  classical
  let C : Finset (Finset Nat) :=
    P.powerset.filter (fun s =>
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true)
  have hEmpty : (∅ : Finset Nat) ∈ C := by
    dsimp only [C]
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset P), ?_⟩
    intro x hx
    simp at hx
  obtain ⟨s, hs, hMax⟩ :=
    Finset.exists_mem_eq_sup C ⟨∅, hEmpty⟩ Finset.card
  have hParts : s ⊆ P ∧ IsDirectedCliqueOn E s := by
    simpa only [C, Finset.mem_filter, Finset.mem_powerset,
      IsDirectedCliqueOn] using hs
  refine ⟨s, hParts.1, hParts.2, ?_⟩
  simpa only [C, finiteDirectedCliqueCapacity] using hMax.symm

/-- The executable exact-size clique checker is negative precisely
when the actual clique capacity is below the tested size.
For size zero both sides are false, since the empty clique exists. -/
theorem finitePoolCliqueCheck_false_iff_capacity_lt
    (E : Nat → Nat → Bool) (ell : Nat) (P : Finset Nat) :
    finitePoolCliqueCheck E ell P = false ↔
      finiteDirectedCliqueCapacity E P < ell := by
  classical
  constructor
  · intro hCheck
    by_contra hNot
    have hLarge : ell ≤ finiteDirectedCliqueCapacity E P :=
      Nat.le_of_not_gt hNot
    obtain ⟨s, hsP, hsClique, hsCard⟩ :=
      finiteDirectedCliqueCapacity_attained E P
    have hSize : ell ≤ s.card := by omega
    obtain ⟨t, htS, htCard⟩ := Finset.exists_subset_card_eq hSize
    have htClique : IsDirectedCliqueOn E t := by
      intro x hx y hy hxy
      exact hsClique x (htS hx) y (htS hy) hxy
    exact ((finitePoolCliqueCheck_false_iff E ell P).1 hCheck)
      ⟨t, htS.trans hsP, htCard, htClique⟩
  · intro hSmall
    apply (finitePoolCliqueCheck_false_iff E ell P).2
    rintro ⟨s, hsP, hsCard, hsClique⟩
    have hBound := directedClique_card_le_capacity E P s hsP hsClique
    omega

/-- Exact clique capacity of a complete directed join of disjoint
finite pools. Neither pool is required to be a clique; both crossing
orientations, and the actual capacities, are essential. -/
theorem finiteDirectedCliqueCapacity_complete_join
    (E : Nat → Nat → Bool) (Q U : Finset Nat)
    (hDisjoint : Disjoint Q U)
    (hJoin :
      ∀ q ∈ Q, ∀ u ∈ U,
        E q u = true ∧ E u q = true) :
    finiteDirectedCliqueCapacity E (Q ∪ U) =
      finiteDirectedCliqueCapacity E Q +
        finiteDirectedCliqueCapacity E U := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨s, hsSub, hsClique, hsCard⟩ :=
      finiteDirectedCliqueCapacity_attained E (Q ∪ U)
    have hCover : s ⊆ (s ∩ Q) ∪ (s ∩ U) := by
      intro x hx
      rcases Finset.mem_union.mp (hsSub hx) with hxQ | hxU
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_inter.mpr ⟨hx, hxQ⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_inter.mpr ⟨hx, hxU⟩))
    have hCoverCard : s.card ≤ ((s ∩ Q) ∪ (s ∩ U)).card :=
      Finset.card_le_card hCover
    have hUnionCard :
        ((s ∩ Q) ∪ (s ∩ U)).card ≤
          (s ∩ Q).card + (s ∩ U).card :=
      Finset.card_union_le _ _
    have hQClique : IsDirectedCliqueOn E (s ∩ Q) := by
      intro x hx y hy hxy
      exact hsClique x (Finset.mem_inter.mp hx).1
        y (Finset.mem_inter.mp hy).1 hxy
    have hUClique : IsDirectedCliqueOn E (s ∩ U) := by
      intro x hx y hy hxy
      exact hsClique x (Finset.mem_inter.mp hx).1
        y (Finset.mem_inter.mp hy).1 hxy
    have hQBound : (s ∩ Q).card ≤ finiteDirectedCliqueCapacity E Q :=
      directedClique_card_le_capacity E Q (s ∩ Q)
        Finset.inter_subset_right hQClique
    have hUBound : (s ∩ U).card ≤ finiteDirectedCliqueCapacity E U :=
      directedClique_card_le_capacity E U (s ∩ U)
        Finset.inter_subset_right hUClique
    omega
  · obtain ⟨sQ, hsQ, hQClique, hQCard⟩ :=
      finiteDirectedCliqueCapacity_attained E Q
    obtain ⟨sU, hsU, hUClique, hUCard⟩ :=
      finiteDirectedCliqueCapacity_attained E U
    have hDisjointCliques : Disjoint sQ sU := by
      apply Finset.disjoint_left.mpr
      intro x hxQ hxU
      exact (Finset.disjoint_left.mp hDisjoint) (hsQ hxQ) (hsU hxU)
    have hUnionSub : sQ ∪ sU ⊆ Q ∪ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxQ | hxU
      · exact Finset.mem_union.mpr (Or.inl (hsQ hxQ))
      · exact Finset.mem_union.mpr (Or.inr (hsU hxU))
    have hUnionClique : IsDirectedCliqueOn E (sQ ∪ sU) := by
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hxQ | hxU
      · rcases Finset.mem_union.mp hy with hyQ | hyU
        · exact hQClique x hxQ y hyQ hxy
        · exact (hJoin x (hsQ hxQ) y (hsU hyU)).1
      · rcases Finset.mem_union.mp hy with hyQ | hyU
        · exact (hJoin y (hsQ hyQ) x (hsU hxU)).2
        · exact hUClique x hxU y hyU hxy
    have hUnionCard : (sQ ∪ sU).card = sQ.card + sU.card :=
      Finset.card_union_of_disjoint hDisjointCliques
    have hBound := directedClique_card_le_capacity
      E (Q ∪ U) (sQ ∪ sU) hUnionSub hUnionClique
    omega

/-- Exact finite continuation criterion for an isolated reserved pool.

The pools P,Q,G,W may overlap: only the two fully joined pools Q,U
must be disjoint. A clique meeting W excludes G OUTSIDE W; if it
also meets Q, it excludes P OUTSIDE Q and its remaining future
vertices belong to U. This proves the needed three-pool reduction
without assuming a partition or an age conclusion.

All Q-to-W bits are prescribed in BOTH directions, including absent
bits outside U. Every gap-to-future zero is required on the entire
displayed G and W. Q need not itself be a clique. -/
theorem finitePoolCliqueCheck_isolated_block_gluing_iff
    (E : Nat → Nat → Bool) (ell : Nat)
    (P Q G W U : Finset Nat)
    (hQU : Disjoint Q U)
    (hU : U ⊆ W)
    (hNoPQ :
      ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (hNoGW :
      ∀ g ∈ G, ∀ w ∈ W, E g w = false)
    (hSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        E q w = decide (w ∈ U) ∧
        E w q = decide (w ∈ U))
    (hPast :
      finitePoolCliqueCheck E ell ((P ∪ Q) ∪ G) = false) :
    finitePoolCliqueCheck E ell (((P ∪ Q) ∪ G) ∪ W) = false ↔
      finitePoolCliqueCheck E ell (P ∪ W) = false ∧
        finiteDirectedCliqueCapacity E Q +
          finiteDirectedCliqueCapacity E U < ell := by
  classical
  have hJoin :
      ∀ q ∈ Q, ∀ u ∈ U, E q u = true ∧ E u q = true := by
    intro q hq u hu
    simpa [hu] using hSupport q hq u (hU hu)
  have hJoinCapacity :
      finiteDirectedCliqueCapacity E (Q ∪ U) =
        finiteDirectedCliqueCapacity E Q +
          finiteDirectedCliqueCapacity E U :=
    finiteDirectedCliqueCapacity_complete_join E Q U hQU hJoin
  have hClassify :
      ∀ s : Finset Nat,
        s ⊆ (((P ∪ Q) ∪ G) ∪ W) →
        IsDirectedCliqueOn E s →
        s ⊆ ((P ∪ Q) ∪ G) ∨
          s ⊆ (P ∪ W) ∨ s ⊆ (Q ∪ U) := by
    intro s hsSub hsClique
    by_cases hHasW : ∃ w ∈ s, w ∈ W
    · obtain ⟨w0, hw0S, hw0W⟩ := hHasW
      have hNoGapOutside :
          ∀ z ∈ s, z ∉ W → z ∉ G := by
        intro z hzS hzNotW hzG
        have hzw : z ≠ w0 := by
          intro hEq
          exact hzNotW (hEq.symm ▸ hw0W)
        have hEdge : E z w0 = true :=
          hsClique z hzS w0 hw0S hzw
        rw [hNoGW z hzG w0 hw0W] at hEdge
        cases hEdge
      by_cases hHasQ : ∃ q ∈ s, q ∈ Q
      · obtain ⟨q0, hq0S, hq0Q⟩ := hHasQ
        right
        right
        intro z hzS
        by_cases hzQ : z ∈ Q
        · exact Finset.mem_union.mpr (Or.inl hzQ)
        · have hzq : z ≠ q0 := by
            intro hEq
            exact hzQ (hEq.symm ▸ hq0Q)
          have hzW : z ∈ W := by
            by_contra hzNotW
            have hzNotG := hNoGapOutside z hzS hzNotW
            rcases Finset.mem_union.mp (hsSub hzS) with hzPast | hzW'
            · rcases Finset.mem_union.mp hzPast with hzPQ | hzG
              · rcases Finset.mem_union.mp hzPQ with hzP | hzQ'
                · have hEdge : E z q0 = true :=
                    hsClique z hzS q0 hq0S hzq
                  rw [hNoPQ z hzP q0 hq0Q] at hEdge
                  cases hEdge
                · exact hzQ hzQ'
              · exact hzNotG hzG
            · exact hzNotW hzW'
          have hEdge : E q0 z = true :=
            hsClique q0 hq0S z hzS (Ne.symm hzq)
          have hDecision : decide (z ∈ U) = true :=
            (hSupport q0 hq0Q z hzW).1.symm.trans hEdge
          have hzU : z ∈ U := by
            simpa only [decide_eq_true_eq] using hDecision
          exact Finset.mem_union.mpr (Or.inr hzU)
      · right
        left
        intro z hzS
        by_cases hzW : z ∈ W
        · exact Finset.mem_union.mpr (Or.inr hzW)
        · have hzNotG := hNoGapOutside z hzS hzW
          rcases Finset.mem_union.mp (hsSub hzS) with hzPast | hzW'
          · rcases Finset.mem_union.mp hzPast with hzPQ | hzG
            · rcases Finset.mem_union.mp hzPQ with hzP | hzQ
              · exact Finset.mem_union.mpr (Or.inl hzP)
              · exact False.elim (hHasQ ⟨z, hzS, hzQ⟩)
            · exact False.elim (hzNotG hzG)
          · exact False.elim (hzW hzW')
    · left
      intro z hzS
      rcases Finset.mem_union.mp (hsSub hzS) with hzPast | hzW
      · exact hzPast
      · exact False.elim (hHasW ⟨z, hzS, hzW⟩)
  constructor
  · intro hFull
    have hFullCapacity :
        finiteDirectedCliqueCapacity E (((P ∪ Q) ∪ G) ∪ W) < ell :=
      (finitePoolCliqueCheck_false_iff_capacity_lt
        E ell (((P ∪ Q) ∪ G) ∪ W)).1 hFull
    have hOldFutureSub : P ∪ W ⊆ (((P ∪ Q) ∪ G) ∪ W) := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzP | hzW
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl hzP)))))
      · exact Finset.mem_union.mpr (Or.inr hzW)
    have hOldFutureCapacity :
        finiteDirectedCliqueCapacity E (P ∪ W) < ell :=
      lt_of_le_of_lt
        (finiteDirectedCliqueCapacity_mono E (P ∪ W)
          (((P ∪ Q) ∪ G) ∪ W) hOldFutureSub)
        hFullCapacity
    have hJoinSub : Q ∪ U ⊆ (((P ∪ Q) ∪ G) ∪ W) := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzQ | hzU
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr hzQ)))))
      · exact Finset.mem_union.mpr (Or.inr (hU hzU))
    have hJoinSmall : finiteDirectedCliqueCapacity E (Q ∪ U) < ell :=
      lt_of_le_of_lt
        (finiteDirectedCliqueCapacity_mono E (Q ∪ U)
          (((P ∪ Q) ∪ G) ∪ W) hJoinSub)
        hFullCapacity
    rw [hJoinCapacity] at hJoinSmall
    exact ⟨(finitePoolCliqueCheck_false_iff_capacity_lt
      E ell (P ∪ W)).2 hOldFutureCapacity, hJoinSmall⟩
  · rintro ⟨hOldFuture, hBudget⟩
    apply (finitePoolCliqueCheck_false_iff
      E ell (((P ∪ Q) ∪ G) ∪ W)).2
    rintro ⟨s, hsSub, hsCard, hsClique⟩
    rcases hClassify s hsSub hsClique with
      hsPast | hsOldFuture | hsJoin
    · exact ((finitePoolCliqueCheck_false_iff
        E ell ((P ∪ Q) ∪ G)).1 hPast)
        ⟨s, hsPast, hsCard, hsClique⟩
    · exact ((finitePoolCliqueCheck_false_iff
        E ell (P ∪ W)).1 hOldFuture)
        ⟨s, hsOldFuture, hsCard, hsClique⟩
    · have hBound := directedClique_card_le_capacity
        E (Q ∪ U) s hsJoin hsClique
      rw [hJoinCapacity] at hBound
      omega

end Kk
