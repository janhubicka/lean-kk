import Kk.PartialNumericSharpLower
import Kk.LinkedCliqueCapacityUpdate
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track A: one-jump exact actual partial numerical-H ordinary-L age profile

English proof and hostile audit committed FIRST:
  docs/partial_numeric_single_jump_english_audit.md

The previously verified actual sharp capacity at a cut before current
original b generation g<=k is max(p, if b is U-eligible then min(g,1+c)
else 0), with p=cap_E(P_U), c=cap_E(S_U), and S_U subset P_U.

Since c<=p, this expression is p+1 precisely if b is eligible,
c=p and p<g, and p otherwise. Hence there is at most one
unit-capacity jump for each fixed nonempty support while g rises
through a single ORIGINAL b block. All old numbered coordinates,
including odd dummy positions, are included in the actual old pool.

The derived raw-age equality, canonicalized integer-age equality
and feasible-vector equality concern the true ordinary binary-L
table against GIVEN later original top names. They do not prove
physical realization of prescribed recursive original columns,
auxiliary E/B3, or a common labelled resolved-copy source.
-/

namespace Kk

open SuccessorTree.V10

/-- Pure finite arithmetic: if c<=p, the max/min candidate has
at most one one-unit jump, at the threshold g=p+1, provided
the current-original eligibility and c=p both hold. -/
theorem partialNumeric_max_min_eq_single_jump
    (p c g : Nat) (hc : c ≤ p)
    (eligible : Prop) [Decidable eligible] :
    max p (if eligible then min g (1+c) else 0) =
      if eligible ∧ c = p ∧ p < g then p+1 else p := by
  by_cases hEligible : eligible
  · by_cases hEq : c = p
    · subst c
      by_cases hPg : p < g
      · have hMin : min g (1+p) = 1+p :=
          min_eq_right (by omega)
        have hMax : max p (1+p) = 1+p :=
          max_eq_right (by omega)
        simp [hEligible,hPg,hMin,hMax] <;> omega
      · have hLe : min g (1+p) ≤ p := by
          have hBound := min_le_left g (1+p)
          omega
        have hMax : max p (min g (1+p)) = p :=
          max_eq_left hLe
        simp [hEligible,hPg,hMax]
    · have hStrict : 1+c ≤ p := by omega
      have hLe : min g (1+c) ≤ p :=
        (min_le_right g (1+c)).trans hStrict
      have hMax : max p (min g (1+c)) = p :=
        max_eq_left hLe
      simp [hEligible,hEq,hMax]
  · simp [hEligible]

/-- Normal-form capacity on a nonempty support U, computed
solely from the original E table and the GIVEN future top names.
It is independent of the arbitrary finite numerical carrier
cutoff M as a Boolean L-table calculation. -/
noncomputable def partialNumericSupportStepCapacity
    {d ell : Nat} (E : Nat → Nat → Bool)
    (b g : Nat) (j : Fin d → Nat)
    (U : IntegerGraphSupport d ell) : Nat := by
  classical
  let P := oldSupportCommonNeighbourPool (Finset.range b)
    (fun i t => E i (j t)) U.1
  let S := P.filter (fun i => E i b = true)
  exact if (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E S =
        finiteDirectedCliqueCapacity E P ∧
      finiteDirectedCliqueCapacity E P < g
    then finiteDirectedCliqueCapacity E P+1
    else finiteDirectedCliqueCapacity E P

/-- TRUE physical partial numerical-H U-common-neighbourhood capacity
has precisely ONE possible unit jump. The proof uses the *verified*
actual sharp finite capacity identity and the monotonicity of clique
capacity under the original S_U subset P_U. -/
theorem finiteNumericH_partial_actual_capacity_eq_single_jump
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
    partialNumericSupportStepCapacity E b g j U := by
  classical
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  have hSub : S ⊆ P := Finset.filter_subset _ _
  have hCapacity :
      finiteDirectedCliqueCapacity E S ≤
        finiteDirectedCliqueCapacity E P :=
    finiteDirectedCliqueCapacity_mono E S P hSub
  have hSharp :=
    finiteNumericH_partial_actual_capacity_eq_sharp
      E hSym k b g M hg j hj U
  have hStep :
      max (finiteDirectedCliqueCapacity E P)
        (if ∀ t ∈ U.1, E b (j t) = true then
          min g (1 + finiteDirectedCliqueCapacity E S)
         else 0) =
      partialNumericSupportStepCapacity E b g j U := by
    exact
      (partialNumeric_max_min_eq_single_jump
        (finiteDirectedCliqueCapacity E P)
        (finiteDirectedCliqueCapacity E S) g hCapacity
        (∀ t ∈ U.1, E b (j t) = true)).trans (by rfl)
  exact hSharp.trans hStep

/-- Exact physical partial-cut raw graph-age normal form.
Only nonempty admissible U are part of IntegerGraphSupport.
Truncated subtraction may hide a capacity jump at age zero. -/
noncomputable def finiteNumericHPartialSingleJumpRawBound
    {d : Nat} (E : Nat → Nat → Bool)
    (ell b g : Nat) (j : Fin d → Nat) :
    IntegerGraphSupport d ell → Nat :=
  fun U => ell - 1 - partialNumericSupportStepCapacity E b g j U

/-- The actual numbered numerical-H ordinary-L old raw age equals
the one-jump ORIGINAL-table formula at EVERY nonempty support. -/
theorem finiteNumericH_partial_actual_raw_age_eq_single_jump
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) =
    finiteNumericHPartialSingleJumpRawBound E ell b g j := by
  funext U
  unfold finiteOldColumnRawBound finiteNumericHPartialSingleJumpRawBound
  rw [finiteNumericH_partial_actual_capacity_eq_single_jump
    E hSym k b g M hg j hj U]

/-- Exact equality of normalized integer graph ages:
the ACTUAL physical partial old-age canonicalization is the
canonicalization of the one-jump raw bound. This does not imply
every capacity jump is a genuine age-cover event. -/
theorem finiteNumericH_partial_actual_canonical_age_eq_single_jump
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1))) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialSingleJumpRawBound E ell b g j) := by
  rw [finiteNumericH_partial_actual_raw_age_eq_single_jump
    E hSym ell k b g M hg j hj]

/-- The feasible normalized integer clique-multiplicity vectors are
exactly those for the M-independent single-jump raw support function.
No physical future realization or labelled source is asserted. -/
theorem finiteNumericH_partial_actual_feasible_eq_single_jump
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1))) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialSingleJumpRawBound E ell b g j) := by
  rw [finiteNumericH_partial_actual_raw_age_eq_single_jump
    E hSym ell k b g M hg j hj]

/-- The ACTUAL partial old raw age is independent of the total
finite Boolean model cutoff M. The corresponding physical carrier
membership requires a separate hypothesis about numeric positions. -/
theorem finiteNumericH_partial_actual_raw_age_cutoff_independent
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M N : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) =
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k N).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k N).binary
          z (hPosition k (j t) k) (0 : Fin 1)) := by
  rw [finiteNumericH_partial_actual_raw_age_eq_single_jump
    E hSym ell k b g M hg j hj]
  rw [finiteNumericH_partial_actual_raw_age_eq_single_jump
    E hSym ell k b g N hg j hj]

#print axioms Kk.partialNumeric_max_min_eq_single_jump
#print axioms Kk.finiteNumericH_partial_actual_capacity_eq_single_jump
#print axioms Kk.finiteNumericH_partial_actual_raw_age_eq_single_jump
#print axioms Kk.finiteNumericH_partial_actual_canonical_age_eq_single_jump
#print axioms Kk.finiteNumericH_partial_actual_feasible_eq_single_jump
#print axioms Kk.finiteNumericH_partial_actual_raw_age_cutoff_independent

end Kk
