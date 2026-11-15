import Kk.PartialNumericCommonPool
import Kk.FullRealGenerationCapacity
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track A: actual partial numerical-H clique capacity bounds

The complete English proof and adversarial checks were committed first:
  docs/partial_numeric_capacity_bounds_english_audit.md

For a TRUE partial original-block cut (before generation g<=k),
the actual all-numbered-coordinate U-common-neighbour pool equals
complete real copies of earlier original U-neighbours, plus current
b copies of generations q<g precisely when the complete U crossing
column of b is positive. Hence its numerical-H clique capacity is
sandwiched between the earlier ORIGINAL capacity and the capacity
after adding original b. When b is not U-eligible, the upper and
lower bounds coincide, giving the exact ORIGINAL capacity.

The sharpened min(g,1+cap(adjacent P)) staircase threshold in
eligible cases is an independent remaining theorem. We do not
infer a global resolved copy, auxiliary E/B3 or Ramsey degrees.
-/

namespace Kk

open SuccessorTree.V10

/-- Actual ordinary-L clique capacity on the literal physical
partial prefix is between the earlier original U-neighbour
capacity and the original capacity after adjoining b.

The upper bound uses the COMPLETE k+1-generation copy pool of
P∪{b} as a genuine superpool; it does not pretend that those
copies already belong to the partial old prefix. -/
theorem finiteNumericH_partial_actual_capacity_sandwich
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1) ≤
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) ∧
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) ≤
    finiteDirectedCliqueCapacity E
      (insert b (oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1)) := by
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
  have hOldSub : numericHCompleteRealPool k P ⊆ N := by
    rw [hExact]
    exact Finset.subset_union_left
  have hEarlierSub :
      numericHCompleteRealPool k P ⊆
        numericHCompleteRealPool k (insert b P) := by
    intro z hz
    obtain ⟨i,hi,q,hq,hEq⟩ :=
      (numericHCompleteRealPool_mem_iff k P z).mp hz
    apply (numericHCompleteRealPool_mem_iff
      k (insert b P) z).mpr
    exact ⟨i,Finset.mem_insert_of_mem hi,q,hq,hEq⟩
  have hCurrentSub :
      (Finset.range g).image (fun q => hPosition k b q) ⊆
        numericHCompleteRealPool k (insert b P) := by
    intro z hz
    obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hz
    have hqLe : q ≤ k := by
      have hqLt : q < g := Finset.mem_range.mp hq
      omega
    apply (numericHCompleteRealPool_mem_iff
      k (insert b P) z).mpr
    exact ⟨b,Finset.mem_insert_self b P,q,hqLe,hEq⟩
  have hNumSub :
      N ⊆ numericHCompleteRealPool k (insert b P) := by
    rw [hExact]
    intro z hz
    rcases Finset.mem_union.mp hz with hOld | hCurrent
    · exact hEarlierSub hOld
    · by_cases hEligible : ∀ t ∈ U.1, E b (j t) = true
      · have hPart :
            z ∈ (Finset.range g).image
              (fun q => hPosition k b q) := by
          simpa [hEligible] using hCurrent
        exact hCurrentSub hPart
      · simp [hEligible] at hCurrent
  have hLower := finiteDirectedCliqueCapacity_mono
    L (numericHCompleteRealPool k P) N hOldSub
  have hUpper := finiteDirectedCliqueCapacity_mono
    L N (numericHCompleteRealPool k (insert b P)) hNumSub
  have hCompleteP :
      finiteDirectedCliqueCapacity L
        (numericHCompleteRealPool k P) =
      finiteDirectedCliqueCapacity E P :=
    finiteNumericH_complete_real_capacity_eq_original E hSym k M P
  have hCompleteQ :
      finiteDirectedCliqueCapacity L
        (numericHCompleteRealPool k (insert b P)) =
      finiteDirectedCliqueCapacity E (insert b P) :=
    finiteNumericH_complete_real_capacity_eq_original
      E hSym k M (insert b P)
  change finiteDirectedCliqueCapacity E P ≤
    finiteDirectedCliqueCapacity L N ∧
    finiteDirectedCliqueCapacity L N ≤
      finiteDirectedCliqueCapacity E (insert b P)
  constructor
  · rw [←hCompleteP]
    exact hLower
  · rw [←hCompleteQ]
    exact hUpper

/-- If the current original b is NOT a common original
neighbour of all U-selected future sorts, *none* of its
partial copies enters the actual old common-neighbour pool.
The capacity is exactly that of earlier originals, for
ANY partial generation cut g<=k. -/
theorem finiteNumericH_partial_actual_capacity_eq_of_ineligible
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell)
    (hIneligible : ¬ ∀ t ∈ U.1, E b (j t) = true) :
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) =
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1) := by
  classical
  have hExact :=
    finiteNumericH_partial_actual_common_pool_explicit
      E hSym k b g M hg j hj U
  have hPool :
      oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1 =
      numericHCompleteRealPool k
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) := by
    simpa [hIneligible] using hExact
  rw [hPool]
  exact finiteNumericH_complete_real_capacity_eq_original
    E hSym k M
      (oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1)

#print axioms Kk.finiteNumericH_partial_actual_capacity_sandwich
#print axioms Kk.finiteNumericH_partial_actual_capacity_eq_of_ineligible

end Kk
