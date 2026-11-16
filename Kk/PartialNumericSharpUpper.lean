import Kk.PartialNumericCurrentLinkUpper
import Kk.PartialNumericGenerationHeight
import Kk.PartialNumericCommonPool
import Kk.FullRealGenerationCapacity
import Mathlib.Tactic

/-!
# Track A: SHARP universal UPPER for actual partial numerical-H old clique capacity

The complete English proof and adversarial audit were committed BEFORE Lean:
  docs/partial_numeric_sharp_upper_english_audit.md

For any nonempty support U, the entire actual numbered prefix's
U-common-neighbourhood capacity is at most
  max(cap_E(P_U), min(g,1+cap_E(S_U))).
Here P_U is the set of all earlier original U-neighbours and S_U
consists of those adjacent to current original b.

If an attaining physical clique has a current b copy, use the two
independently formalized physical upper bounds:
  card ≤ g  (generation injection below non-top b),
  card ≤ 1+cap_E(S_U) (original neighbour projection).
Otherwise the clique lies in the complete real copies of P_U,
whose exact capacity is cap_E(P_U).

This is a SHARP UPPER only: the staircase LOWER witness,
actual recursive original selection and dependent Kpt E/B3
source remain separate obligations.
-/

namespace Kk

open SuccessorTree.V10

/-- Every actual physical old partial-prefix U-neighbourhood
has maximum directed binary-L clique capacity bounded by
the sharp pointwise numerical min/max expression.

The value on the RHS is a *candidate exact formula*; this
theorem proves only the upper inequality, not equality. -/
theorem finiteNumericH_partial_actual_capacity_le_sharp
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) ≤
    max
      (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1))
      (min g (1 + finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)))) := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1)
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1
  let N : Finset Nat :=
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => L z (hPosition k (j t) k)) U.1
  have hExact :
      N = numericHCompleteRealPool k P ∪
        (if ∀ t ∈ U.1, E b (j t) = true then
          (Finset.range g).image (fun q => hPosition k b q)
         else ∅) :=
    finiteNumericH_partial_actual_common_pool_explicit
      E hSym k b g M hg j hj U
  have hNReal : N ⊆ numericHPartialRealPool k b g := by
    intro z hz
    have hPhysical :=
      finiteNumericH_partial_actual_common_pool_eq
        E hSym k b g M hg j hj U
    rw [hPhysical] at hz
    exact (Finset.mem_filter.mp hz).1
  have hNFull :
      N ⊆ numericHCompleteRealPool k P ∪
        (Finset.range g).image (fun q => hPosition k b q) := by
    rw [hExact]
    intro z hz
    rcases Finset.mem_union.mp hz with hOld | hCurrent
    · exact Finset.mem_union.mpr (Or.inl hOld)
    · by_cases hEligible : ∀ t ∈ U.1, E b (j t) = true
      · have hPart :
            z ∈ (Finset.range g).image
              (fun q => hPosition k b q) := by
          simpa only [if_pos hEligible] using hCurrent
        exact Finset.mem_union.mpr (Or.inr hPart)
      · simp [hEligible] at hCurrent
  obtain ⟨s,hs,hClique,hCard⟩ :=
    finiteDirectedCliqueCapacity_attained L N
  have hsReal : s ⊆ numericHPartialRealPool k b g :=
    hs.trans hNReal
  have hsFull :
      s ⊆ numericHCompleteRealPool k P ∪
        (Finset.range g).image (fun q => hPosition k b q) :=
    hs.trans hNFull
  by_cases hCurrent :
      ∃ m : Nat, m < g ∧ hPosition k b m ∈ s
  · obtain ⟨m,hm,hmS⟩ := hCurrent
    have hHeight :=
      finiteNumericH_partial_current_clique_card_le_cut
        E hSym k b g M hg s hsReal hClique m hm hmS
    have hLinked :=
      finiteNumericH_partial_current_clique_card_le_link_cap
        E k b g M hg P s hsFull hClique m hm hmS
    have hMin : s.card ≤
        min g (1 + finiteDirectedCliqueCapacity E
          (P.filter (fun i => E i b = true))) :=
      Nat.le_min.mpr ⟨hHeight,hLinked⟩
    have hUpper : s.card ≤
        max (finiteDirectedCliqueCapacity E P)
          (min g (1 + finiteDirectedCliqueCapacity E
            (P.filter (fun i => E i b = true)))) :=
      le_trans hMin (le_max_right _ _)
    change finiteDirectedCliqueCapacity L N ≤
      max (finiteDirectedCliqueCapacity E P)
        (min g (1 + finiteDirectedCliqueCapacity E
          (P.filter (fun i => E i b = true))))
    omega
  · have hsOld : s ⊆ numericHCompleteRealPool k P := by
      intro z hzS
      rcases Finset.mem_union.mp (hsFull hzS) with hOld | hPartial
      · exact hOld
      · obtain ⟨m,hm,hEq⟩ := Finset.mem_image.mp hPartial
        have hmS : hPosition k b m ∈ s := by
          rw [hEq]
          exact hzS
        exact False.elim (hCurrent
          ⟨m,Finset.mem_range.mp hm,hmS⟩)
    have hBound :=
      directedClique_card_le_capacity L
        (numericHCompleteRealPool k P) s hsOld hClique
    have hComplete :
        finiteDirectedCliqueCapacity L
          (numericHCompleteRealPool k P) =
        finiteDirectedCliqueCapacity E P :=
      finiteNumericH_complete_real_capacity_eq_original
        E hSym k M P
    rw [hComplete] at hBound
    have hUpper : s.card ≤
        max (finiteDirectedCliqueCapacity E P)
          (min g (1 + finiteDirectedCliqueCapacity E
            (P.filter (fun i => E i b = true)))) :=
      le_trans hBound (le_max_left _ _)
    change finiteDirectedCliqueCapacity L N ≤
      max (finiteDirectedCliqueCapacity E P)
        (min g (1 + finiteDirectedCliqueCapacity E
          (P.filter (fun i => E i b = true))))
    omega

#print axioms Kk.finiteNumericH_partial_actual_capacity_le_sharp

end Kk
