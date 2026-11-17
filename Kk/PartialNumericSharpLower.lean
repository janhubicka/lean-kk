import Kk.OrderedCliquePrefixWitness
import Kk.PartialNumericStaircaseLower
import Kk.PartialNumericSharpUpper
import Kk.PartialNumericCapacityBounds
import Mathlib.Tactic

/-!
# Track A: exact conditional sharp physical partial-cut numerical-H age

The complete English proof, hostile audit and essential
INELIGIBLE-CURRENT-ORIGINAL counterexample were committed first:
  docs/partial_numeric_sharp_lower_english_audit.md

Let P_U be earlier original U-common neighbours, S_U those also
originally adjacent to current b, and N_U the TRUE actual
numbered prefix U-common-neighbourhood before generation g<=k.
The *correct* sharp capacity is

 cap_L(N_U) =
   max(cap_E(P_U),
     if b is U-eligible then min(g,1+cap_E(S_U)) else 0).

An unconditional extra min term would be false for an ineligible
current b; the English audit gives a 3-original K4-free counterexample.

Lower bound: choose an attained maximum E clique in S_U,
take its first a=min(cap_E(S_U),g-1) original names in strict
natural order (OrderedCliquePrefixWitness), append b, then
apply the true nonconsecutive physical staircase lower theorem.
Upper bound: sharp physical capacity upper plus separate ineligible
exact equality. No infinite schedule, Kpt E/B3 or BRD is claimed.
-/

namespace Kk

open SuccessorTree.V10

/-- If current original b has the FULL positive original column
to every selected top sort in nonempty U, the actual numbered
partial old U-common-neighbour clique capacity is at least the
sharp max of the original old capacity and the non-top staircase
capacity. This includes g=0 (no current b copy in the old prefix). -/
theorem finiteNumericH_partial_actual_capacity_ge_sharp_of_eligible
    {d ell : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell)
    (hEligible : ∀ t ∈ U.1, E b (j t) = true) :
    max
      (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1))
      (min g (1 + finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
            (fun i => E i b = true)))) ≤
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
      (fun i t => E i (j t)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  let N : Finset Nat :=
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => L z (hPosition k (j t) k)) U.1
  have hFirst : finiteDirectedCliqueCapacity E P ≤
      finiteDirectedCliqueCapacity L N :=
    (finiteNumericH_partial_actual_capacity_sandwich
      E hSym k b g M hg j hj U).1
  change max (finiteDirectedCliqueCapacity E P)
    (min g (1 + finiteDirectedCliqueCapacity E S)) ≤
      finiteDirectedCliqueCapacity L N
  by_cases hg0 : g = 0
  · simpa [hg0] using hFirst
  · let c : Nat := finiteDirectedCliqueCapacity E S
    let a : Nat := min c (g-1)
    have haC : a ≤ finiteDirectedCliqueCapacity E S := by
      dsimp [a,c]
      exact Nat.min_le_left _ _
    have haG : a < g := by
      have hLe : a ≤ g-1 := Nat.min_le_right _ _
      omega
    have hMin : a+1 = min g (1+finiteDirectedCliqueCapacity E S) := by
      change min c (g-1)+1 = min g (1+c)
      omega
    have hBefore : ∀ i ∈ S, i < b := by
      intro i hi
      have hiP : i ∈ P := (Finset.mem_filter.mp hi).1
      exact Finset.mem_range.mp
        (Finset.mem_filter.mp hiP).1
    have hLink : ∀ i ∈ S, E i b = true := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    obtain ⟨q,hLast,hInS,hOrder,hClique⟩ :=
      finiteDirectedCliqueCapacity_increasing_prefix_append
        E S b a hBefore hLink haC
    have hEarlier : ∀ i, i < a →
        q i ∈ oldSupportCommonNeighbourPool (Finset.range b)
          (fun x t => E x (j t)) U.1 := by
      intro i hi
      exact (Finset.mem_filter.mp (hInS i hi)).1
    have hPhysical :=
      finiteNumericH_partial_actual_capacity_ge_staircase
        E hSym k b g M hg j hj U hEligible
        a haG q hLast hEarlier hOrder hClique
    have hSecond : min g
        (1+finiteDirectedCliqueCapacity E S) ≤
        finiteDirectedCliqueCapacity L N := by
      rw [←hMin]
      exact hPhysical
    exact max_le hFirst hSecond

/-- COMPLETE EXACT physical partial old capacity formula.
The conditional b-eligibility is mathematical, not optional:
if b is not an U-common neighbour the extra staircase term
must be ZERO. This theorem concerns ordinary numerical H L;
the full dependent Kpt E/B3 source is a separate problem. -/
theorem finiteNumericH_partial_actual_capacity_eq_sharp
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
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) =
    max
      (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1))
      (if ∀ t ∈ U.1, E b (j t) = true then
        min g (1 + finiteDirectedCliqueCapacity E
          ((oldSupportCommonNeighbourPool (Finset.range b)
            (fun i t => E i (j t)) U.1).filter
              (fun i => E i b = true)))
       else 0) := by
  classical
  by_cases hEligible : ∀ t ∈ U.1, E b (j t) = true
  · have hUpper :=
      finiteNumericH_partial_actual_capacity_le_sharp
        E hSym k b g M hg j hj U
    have hLower :=
      finiteNumericH_partial_actual_capacity_ge_sharp_of_eligible
        E hSym k b g M hg j hj U hEligible
    simp only [if_pos hEligible]
    exact Nat.le_antisymm hUpper hLower
  · have hExact :=
      finiteNumericH_partial_actual_capacity_eq_of_ineligible
        E hSym k b g M hg j hj U hEligible
    simpa [hEligible] using hExact

#print axioms Kk.finiteNumericH_partial_actual_capacity_ge_sharp_of_eligible
#print axioms Kk.finiteNumericH_partial_actual_capacity_eq_sharp

end Kk
