import Kk.PartialNumericSingleJumpAge
import Mathlib.Tactic

/-!
# Track A: exact actual partial-cut RAW-support change events

English proof and seventeen adversarial checks were committed first:
  docs/partial_numeric_raw_support_events_english_audit.md

For any nonempty admissible U and GIVEN later top original names,
the true old numerical-H raw support age strictly decreases from
cut g to cut h (g<=h<=k) iff ALL hold:

* current b is U-eligible;
* c_U=cap_E(S_U) equals p_U=cap_E(P_U);
* g<=p_U<h, so the cuts straddle the sole possible height p_U+1;
* p_U<ell-1, so raw truncated subtraction is not already zero.

When it changes it decreases by EXACTLY ONE. This is a RAW
ordinary-L support event, NOT an asserted canonical age cover,
full auxiliary Kpt E/B3 event or global diary/orbit theorem.
-/

namespace Kk

open SuccessorTree.V10

/-- Arithmetic iff for a strict raw-age decrease between
two one-jump capacity bounds, including truncated subtraction.
The necessary p<ell-1 clause cannot be omitted. -/
theorem partialNumeric_raw_event_arithmetic_iff
    (ell p c g h : Nat) (hgh : g ≤ h)
    (eligible : Prop) [Decidable eligible] :
    ell-1 -
        (if eligible ∧ c = p ∧ p < h then p+1 else p) <
      ell-1 -
        (if eligible ∧ c = p ∧ p < g then p+1 else p) ↔
      eligible ∧ c = p ∧ g ≤ p ∧ p < h ∧ p < ell-1 := by
  by_cases he : eligible <;>
    by_cases hc : c = p <;>
    by_cases hg : p < g <;>
    by_cases hh : p < h <;>
    simp [he,hc,hg,hh] <;> omega

/-- Any genuine strict raw step in the one-jump arithmetic
has exact size one, not merely positive difference. -/
theorem partialNumeric_raw_event_arithmetic_unit
    (ell p c g h : Nat) (hgh : g ≤ h)
    (eligible : Prop) [Decidable eligible]
    (hEvent :
      ell-1 -
          (if eligible ∧ c = p ∧ p < h then p+1 else p) <
        ell-1 -
          (if eligible ∧ c = p ∧ p < g then p+1 else p)) :
    ell-1 -
        (if eligible ∧ c = p ∧ p < g then p+1 else p) =
      ell-1 -
        (if eligible ∧ c = p ∧ p < h then p+1 else p) + 1 := by
  obtain ⟨he,hc,hgp,hph,hBound⟩ :=
    (partialNumeric_raw_event_arithmetic_iff
      ell p c g h hgh eligible).mp hEvent
  have hOld : ¬ (eligible ∧ c = p ∧ p < g) := by
    intro hx
    omega
  have hNew : eligible ∧ c = p ∧ p < h := ⟨he,hc,hph⟩
  simp only [if_neg hOld, if_pos hNew]
  omega

/-- EXACT necessary-and-sufficient condition for a strict raw
age decrease on any nonempty support U between two physical
partial original-block cuts against the SAME given future tops.
This does NOT determine a canonical cover or dependent B3 event. -/
theorem finiteNumericH_partial_actual_raw_support_event_iff
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b h))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U <
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U ↔
    (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
          (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < ell-1 := by
  classical
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  let p : Nat := finiteDirectedCliqueCapacity E P
  let c : Nat := finiteDirectedCliqueCapacity E S
  let eligible : Prop := ∀ t ∈ U.1, E b (j t) = true
  have hg : g ≤ k := hgh.trans hh
  have hRawH := congrFun
    (finiteNumericH_partial_actual_raw_age_eq_single_jump
      E hSym ell k b h M hh j hj) U
  have hRawG := congrFun
    (finiteNumericH_partial_actual_raw_age_eq_single_jump
      E hSym ell k b g M hg j hj) U
  rw [hRawH,hRawG]
  change ell-1 -
      (if eligible ∧ c = p ∧ p < h then p+1 else p) <
    ell-1 -
      (if eligible ∧ c = p ∧ p < g then p+1 else p) ↔
      eligible ∧ c = p ∧ g ≤ p ∧ p < h ∧ p < ell-1
  exact partialNumeric_raw_event_arithmetic_iff
    ell p c g h hgh eligible

/-- Every physical raw support decrease between two partial
cutoffs is by precisely one unit. The result is silent on
whether normalized canonical ages form a cover. -/
theorem finiteNumericH_partial_actual_raw_support_event_unit
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (U : IntegerGraphSupport d ell)
    (hEvent :
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b h))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U <
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U =
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b h))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U + 1 := by
  classical
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i t => E i (j t)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  let p : Nat := finiteDirectedCliqueCapacity E P
  let c : Nat := finiteDirectedCliqueCapacity E S
  let eligible : Prop := ∀ t ∈ U.1, E b (j t) = true
  have hg : g ≤ k := hgh.trans hh
  have hRawH := congrFun
    (finiteNumericH_partial_actual_raw_age_eq_single_jump
      E hSym ell k b h M hh j hj) U
  have hRawG := congrFun
    (finiteNumericH_partial_actual_raw_age_eq_single_jump
      E hSym ell k b g M hg j hj) U
  rw [hRawG,hRawH] at hEvent ⊢
  change ell-1 -
      (if eligible ∧ c = p ∧ p < h then p+1 else p) <
    ell-1 -
      (if eligible ∧ c = p ∧ p < g then p+1 else p) at hEvent
  change ell-1 -
      (if eligible ∧ c = p ∧ p < g then p+1 else p) =
    ell-1 -
      (if eligible ∧ c = p ∧ p < h then p+1 else p) + 1
  exact partialNumeric_raw_event_arithmetic_unit
    ell p c g h hgh eligible hEvent

#print axioms Kk.partialNumeric_raw_event_arithmetic_iff
#print axioms Kk.partialNumeric_raw_event_arithmetic_unit
#print axioms Kk.finiteNumericH_partial_actual_raw_support_event_iff
#print axioms Kk.finiteNumericH_partial_actual_raw_support_event_unit

end Kk
