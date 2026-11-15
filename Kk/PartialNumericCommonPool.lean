import Kk.PartialNumericOldColumns
import Kk.FullRealGenerationCapacity
import Mathlib.Tactic

/-!
# Track A: explicit all-support actual partial numerical-H common pool

English-first proof and adversarial audit:
  docs/partial_numeric_common_pool_english_audit.md

The TRUE old numbered prefix's common-neighbourhood for a nonempty
support U is the union of the complete real-generation copies of
old ORIGINAL U-neighbours and, precisely when the current original
b has the full U column, ALL g strictly earlier generations of b.
Odd dummy coordinates do not enter the common-neighbourhood.

This is equality of FINITE VERTEX POOLS, not a numerical assertion
about their clique capacity, a graph-age cover or the full dependent
Kpt E/parameter-closed source.
-/

namespace Kk

open SuccessorTree.V10

/-- Exact *actual* old U-common-neighbour vertex pool at a
partial original-block cut before generation g<=k. The second
component is either every generation q<g of the current original
b or the empty set; this is decided by its complete original
crossing column to all future top sorts in U.

The partial cut excludes b's TOP generation and includes every
numbered odd dummy, but all odd dummies vanish from this equality
because U is a nonempty IntegerGraphSupport. -/
theorem finiteNumericH_partial_actual_common_pool_explicit
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U.1 =
    numericHCompleteRealPool k
      (oldSupportCommonNeighbourPool (Finset.range b)
        (fun i t => E i (j t)) U.1) ∪
    (if ∀ t ∈ U.1, E b (j t) = true then
       (Finset.range g).image (fun q => hPosition k b q)
     else ∅) := by
  classical
  rw [finiteNumericH_partial_actual_common_pool_eq
    E hSym k b g M hg j hj U]
  ext z
  constructor
  · intro hz
    obtain ⟨hzReal,hAll⟩ := Finset.mem_filter.mp hz
    have hSplit :
        z ∈ numericHCompleteRealPool k (Finset.range b) ∪
          (Finset.range g).image (fun q => hPosition k b q) := by
      rw [←numericH_partial_real_pool_exact k b g hg]
      exact hzReal
    rcases Finset.mem_union.mp hSplit with hOld | hCurrent
    · obtain ⟨i,hi,q,hq,hEq⟩ :=
        (numericHCompleteRealPool_mem_iff
          k (Finset.range b) z).mp hOld
      have hDecode : numericHRealOriginal k z = i := by
        rw [←hEq]
        exact numericHRealOriginal_at k i q hq
      have hAllOld : ∀ t ∈ U.1, E i (j t) = true := by
        intro t ht
        have hVal := hAll t ht
        simpa [numericHPartialOldColumn,hzReal,hDecode]
          using hVal
      apply Finset.mem_union.mpr
      left
      apply (numericHCompleteRealPool_mem_iff k
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) z).mpr
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hAllOld⟩,q,hq,hEq⟩
    · obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hCurrent
      have hqLe : q ≤ k := by
        have hqLt : q < g := Finset.mem_range.mp hq
        omega
      have hDecode : numericHRealOriginal k z = b := by
        rw [←hEq]
        exact numericHRealOriginal_at k b q hqLe
      have hEligible : ∀ t ∈ U.1, E b (j t) = true := by
        intro t ht
        have hVal := hAll t ht
        simpa [numericHPartialOldColumn,hzReal,hDecode]
          using hVal
      apply Finset.mem_union.mpr
      right
      simpa [hEligible] using hCurrent
  · intro hz
    rcases Finset.mem_union.mp hz with hOld | hCurrent
    · obtain ⟨i,hi,q,hq,hEq⟩ :=
        (numericHCompleteRealPool_mem_iff k
          (oldSupportCommonNeighbourPool (Finset.range b)
            (fun i t => E i (j t)) U.1) z).mp hOld
      obtain ⟨hiOld,hAll⟩ := Finset.mem_filter.mp hi
      have hEarlier : z ∈
          numericHCompleteRealPool k (Finset.range b) :=
        (numericHCompleteRealPool_mem_iff
          k (Finset.range b) z).mpr ⟨i,hiOld,q,hq,hEq⟩
      have hzReal : z ∈ numericHPartialRealPool k b g := by
        rw [numericH_partial_real_pool_exact k b g hg]
        exact Finset.mem_union.mpr (Or.inl hEarlier)
      have hDecode : numericHRealOriginal k z = i := by
        rw [←hEq]
        exact numericHRealOriginal_at k i q hq
      apply Finset.mem_filter.mpr
      refine ⟨hzReal,?_⟩
      intro t ht
      have hVal := hAll t ht
      simpa [numericHPartialOldColumn,hzReal,hDecode]
        using hVal
    · by_cases hEligible : ∀ t ∈ U.1, E b (j t) = true
      · have hzCurrent :
            z ∈ (Finset.range g).image
              (fun q => hPosition k b q) := by
          simpa only [if_pos hEligible] using hCurrent
        obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hzCurrent
        have hqLe : q ≤ k := by
          have hqLt : q < g := Finset.mem_range.mp hq
          omega
        have hzReal : z ∈ numericHPartialRealPool k b g := by
          rw [numericH_partial_real_pool_exact k b g hg]
          exact Finset.mem_union.mpr (Or.inr hzCurrent)
        have hDecode : numericHRealOriginal k z = b := by
          rw [←hEq]
          exact numericHRealOriginal_at k b q hqLe
        apply Finset.mem_filter.mpr
        refine ⟨hzReal,?_⟩
        intro t ht
        have hVal := hEligible t ht
        simpa [numericHPartialOldColumn,hzReal,hDecode]
          using hVal
      · simp [hEligible] at hCurrent

#print axioms Kk.finiteNumericH_partial_actual_common_pool_explicit

end Kk
