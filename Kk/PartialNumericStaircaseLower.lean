import Kk.PartialNumericSharpUpper
import Kk.NonconsecutiveReservedPrefix
import Kk.PartialNumericCommonPool
import Mathlib.Tactic

/-!
# Track A: literal partial numerical-H staircase LOWER witness

English proof and adversarial checks committed before Lean:
  docs/partial_numeric_staircase_lower_english_audit.md

For any explicitly given strictly increasing ORIGINAL E clique
q(0),...,q(a)=b of length a+1 whose first a vertices belong
to the earlier U-common-neighbour pool P_U, with b itself
U-eligible and a<g<=k, the ACTUAL partial old numbered
U-neighbourhood contains a true numerical-H clique of size
a+1. The existing independently proved nonconsecutive
reserved-prefix capacity theorem constructs the physical
staircase witness; the only missing work is showing that
its exact literal real-copy pool lies in the U-neighbourhood.

This is a conditional LOWER statement: extracting the needed
ordered clique q from cap_E(S_U) is a separate remaining lemma.
-/

namespace Kk

open SuccessorTree.V10

/-- Given an increasing original E clique ending at current
original b, with all earlier names actual U-common neighbours,
the physical partial numeric old U-neighbourhood contains
a directed-L clique of the same cardinal a+1. The current
generation threshold g strictly exceeds a, so the certified
numerical staircase of heights 0,...,a lies below the cut. -/
theorem finiteNumericH_partial_actual_capacity_ge_staircase
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell)
    (hEligible : ∀ t ∈ U.1, E b (j t) = true)
    (a : Nat) (ha : a < g)
    (q : Nat → Nat)
    (hLast : q a = b)
    (hEarlier : ∀ i, i < a →
      q i ∈ oldSupportCommonNeighbourPool (Finset.range b)
        (fun x t => E x (j t)) U.1)
    (hOrder : ∀ x y, x < y → y < a+1 → q x < q y)
    (hClique : ∀ x y, x < y → y < a+1 →
      E (q x) (q y) = true) :
    a+1 ≤
      finiteDirectedCliqueCapacity
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        (oldSupportCommonNeighbourPool
          (Finset.range (hPosition k b g))
          (fun z t => (finiteNumericHL
            (normalizedGraphModel E) k M).binary
              z (hPosition k (j t) k) (0 : Fin 1)) U.1) := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1)
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun x t => E x (j t)) U.1
  let N : Finset Nat :=
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => L z (hPosition k (j t) k)) U.1
  have hExact :
      N = numericHCompleteRealPool k P ∪
        (if ∀ t ∈ U.1, E b (j t) = true then
           (Finset.range g).image (fun m => hPosition k b m)
         else ∅) :=
    finiteNumericH_partial_actual_common_pool_explicit
      E hSym k b g M hg j hj U
  have hSub : orderedReservedNumericPrefix k q a a ⊆ N := by
    intro z hz
    obtain ⟨x,hx,hEq⟩ := Finset.mem_image.mp hz
    have hFilter := Finset.mem_filter.mp hx
    have hProduct := Finset.mem_product.mp hFilter.1
    have hGenBound : x.2 ≤ k := by
      have hLt := Finset.mem_range.mp hProduct.2
      omega
    rw [hExact]
    rcases hFilter.2 with hOld | ⟨hCurrent,hCurrentGen⟩
    · have hOriginal : q x.1 ∈ P := hEarlier x.1 hOld
      have hCopy :
          z ∈ numericHCompleteRealPool k P := by
        apply (numericHCompleteRealPool_mem_iff k P z).mpr
        refine ⟨q x.1,hOriginal,x.2,hGenBound,?_⟩
        simpa only [orderedReservedNumericPos] using hEq
      exact Finset.mem_union.mpr (Or.inl hCopy)
    · have hName : q x.1 = b := by
        rw [hCurrent]
        exact hLast
      have hGen : x.2 < g := by omega
      have hCoord : hPosition k b x.2 = z := by
        simpa only [orderedReservedNumericPos,hName] using hEq
      have hPart :
          z ∈ (Finset.range g).image
            (fun m => hPosition k b m) :=
        Finset.mem_image.mpr
          ⟨x.2,Finset.mem_range.mpr hGen,hCoord⟩
      apply Finset.mem_union.mpr
      right
      simpa [hEligible] using hPart
  have hCapacity :
      finiteDirectedCliqueCapacity L
        (orderedReservedNumericPrefix k q a a) = a+1 := by
    have h :=
      finiteNumericH_ordered_reserved_prefix_capacity
        E hSym k M (a+1) a a q
        (by omega) (by omega) (by omega)
        hOrder hClique
    simpa using h
  have hMono : finiteDirectedCliqueCapacity L
      (orderedReservedNumericPrefix k q a a) ≤
      finiteDirectedCliqueCapacity L N :=
    finiteDirectedCliqueCapacity_mono L
      (orderedReservedNumericPrefix k q a a) N hSub
  rw [hCapacity] at hMono
  change a+1 ≤ finiteDirectedCliqueCapacity L N
  exact hMono

#print axioms Kk.finiteNumericH_partial_actual_capacity_ge_staircase

end Kk
