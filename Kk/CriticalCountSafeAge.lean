import Kk.OriginalCriticalCount
import Mathlib.Tactic

/-!
# Track B: genuine K_ell-free final prefixes detect EVERY critical old-original event

English proof and adversarial audit committed first:
docs/track_b_critical_neutral_cover_english_audit.md

The previously checked critical-count identity uses natural truncated
subtraction. The exact ORIGINAL clique capacity increases by exactly the critical
original count, without truncation. A genuinely K_ell-free final old
original prefix then bounds the final capacity by ell-1. This yields
an exact raw-age conservation law EVEN WHEN the final raw bound is zero.

This yields the exact nontruncated conservation identity:
  initial raw age = number of critical originals + final raw age.

Zero critical counts on ALL actual supports suffice to preserve the
whole raw and canonical reference ages over any FINITE original interval.
The result does NOT say that the canonical diary constructs such a
neutral interval or that full dependent Kpt L+ events are matched.
-/

namespace Kk

/-- Exact one-original update of a TRUE common old-neighbour clique
capacity. The capacity grows by exactly one iff the new original is
critical on the WHOLE supported sort set U, otherwise stays unchanged.
This holds in arbitrary directed graphs, without K_ell-free safety. -/
theorem oldSupportCommonCapacity_insert_critical_exact
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P) :
    finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (insert v P) c U.1) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) +
      (by
        classical
        exact if originalCriticalSupport E P c U v then 1 else 0) := by
  classical
  change finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (insert v P) c U.1) =
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c U.1) +
      (if originalCriticalSupport E P c U v then 1 else 0)
  rw [oldSupportCommonNeighbourPool_insert_exact]
  by_cases hLive : ∀ t ∈ U.1, c v t = true
  · simp only [if_pos hLive]
    have hvPool : v ∉ oldSupportCommonNeighbourPool P c U.1 := by
      intro hx
      exact hv (Finset.mem_filter.mp hx).1
    rw [finiteDirectedCliqueCapacity_insert_one_jump
      E (oldSupportCommonNeighbourPool P c U.1) v hvPool]
    by_cases hEq : finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c U.1) v) =
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1)
    · have hCrit : originalCriticalSupport E P c U v := ⟨hLive, hEq⟩
      simp only [if_pos hEq, if_pos hCrit]
    · have hNotCrit : ¬ originalCriticalSupport E P c U v := by
        intro h
        exact hEq h.2
      simp only [if_neg hEq, if_neg hNotCrit]
      omega
  · have hNotCrit : ¬ originalCriticalSupport E P c U v := by
      intro h
      exact hLive h.1
    simp only [if_neg hLive, if_neg hNotCrit]
    omega

/-- Exact finite chronological telescope for COMMON ORIGINAL CLIQUE
CAPACITIES, before applying natural truncated subtraction.

The final capacity equals initial capacity plus the number of
critical original insertions at U. No K_ell-freeness is needed.
This is stronger than the previously verified raw-bound telescope. -/
theorem oldSupportCommonCapacity_eq_add_criticalCount
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) :
    finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1) +
      originalCriticalCount E ell d b c U m := by
  classical
  induction m with
  | zero =>
      simp [originalCriticalCount]
  | succ m ih =>
      have hRange :
          Finset.range (b+(m+1)) =
            insert (b+m) (Finset.range (b+m)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hRange]
      have hFresh : b+m ∉ Finset.range (b+m) := by simp
      rw [oldSupportCommonCapacity_insert_critical_exact
        E ell d (Finset.range (b+m)) c U (b+m) hFresh]
      rw [originalCriticalCount_succ]
      change
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1) +
          (if originalCriticalSupport E (Finset.range (b+m))
                c U (b+m) then 1 else 0) =
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c U.1) +
        (originalCriticalCount E ell d b c U m +
          (if originalCriticalSupport E (Finset.range (b+m))
                c U (b+m) then 1 else 0))
      omega

/-- Genuine K_ell-free safety of the entire FINAL original prefix
bounds its full common-old-neighbour clique capacity strictly below ell.

NOTE: This does NOT assert a positive RAW bound: capacity ell-1 is
allowed and the raw continuation bound can equal zero. -/
theorem oldSupportCommonCapacity_lt_ell_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1) < ell := by
  classical
  have hSub :
      oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1 ⊆
        Finset.range (b+m) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hCapLe := finiteDirectedCliqueCapacity_mono E
    (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1)
    (Finset.range (b+m)) hSub
  have hCapLt :
      finiteDirectedCliqueCapacity E (Finset.range (b+m)) < ell :=
    (finitePoolCliqueCheck_false_iff_capacity_lt
      E ell (Finset.range (b+m))).mp hSafe
  omega

/-- TRUE K_ell-free final original-prefix safety eliminates saturation
ambiguity through the EXACT untruncated capacity telescope, even when
the final raw continuation bound is zero.

Therefore initial raw age equals critical count plus final raw age. -/
theorem originalCriticalCount_add_final_raw_eq_initial_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    originalCriticalCount E ell d b c U m +
      finiteOldColumnRawBound E ell d (Finset.range (b+m)) c U =
      finiteOldColumnRawBound E ell d (Finset.range b) c U := by
  have hCapTel := oldSupportCommonCapacity_eq_add_criticalCount
    E ell d b m c U
  have hCapLt := oldSupportCommonCapacity_lt_ell_of_safe
    E ell d b m c U hSafe
  change originalCriticalCount E ell d b c U m +
    (ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1)) =
    ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1)
  omega

/-- Under genuine full-prefix safety, a support's literal RAW bound
stays constant across an actual original interval IFF there are
no critical original insertions at that support.

This is emphatically NOT an iff for equality of CANONICAL ages. -/
theorem originalCriticalCount_zero_iff_raw_eq_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    originalCriticalCount E ell d b c U m = 0 ↔
      finiteOldColumnRawBound E ell d (Finset.range (b+m)) c U =
        finiteOldColumnRawBound E ell d (Finset.range b) c U := by
  have hConservation := originalCriticalCount_add_final_raw_eq_initial_of_safe
    E ell d b m c U hSafe
  constructor
  · intro hZero
    omega
  · intro hEq
    omega

/-- No critical actual originals on ANY supported future sort set
implies equality of the ENTIRE literal RAW reference-age functions.

Unlike the converse, this sufficient direction does not need
a forbidden-free final prefix. -/
theorem finiteOldColumnRawBound_interval_eq_of_zero_critical_count
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hZero : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m = 0) :
    finiteOldColumnRawBound E ell d (Finset.range (b+m)) c =
      finiteOldColumnRawBound E ell d (Finset.range b) c := by
  funext U
  rw [finiteOldColumnRawBound_eq_sub_criticalCount E ell d b m c U,
    hZero U]
  simp

/-- Equality of entire literal RAW reference-age functions is
equivalent to zero critical ORIGINAL events on every support,
provided the final entire old original prefix is K_ell-free. -/
theorem all_critical_count_zero_iff_raw_interval_eq_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    (∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m = 0) ↔
      finiteOldColumnRawBound E ell d (Finset.range (b+m)) c =
        finiteOldColumnRawBound E ell d (Finset.range b) c := by
  constructor
  · exact finiteOldColumnRawBound_interval_eq_of_zero_critical_count
      E ell d b m c
  · intro hEq U
    exact (originalCriticalCount_zero_iff_raw_eq_of_safe
      E ell d b m c U hSafe).2 (congrFun hEq U)

/-- If every admissible support has zero critical originals in
the same actual finite interval, the ENTIRE canonical old-age
function also stays equal. Does NOT hold conversely in general. -/
theorem integerGraphAgeCanonical_interval_eq_of_zero_critical_count
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hZero : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m = 0) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
      integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  rw [finiteOldColumnRawBound_interval_eq_of_zero_critical_count
    E ell d b m c hZero]

/-- The hPrior invariant required by the later ACTUAL Henson
canonical-cover construction is preserved after a fixed-column
finite stretch with NO actual raw critical-original events.

No claim is made about changing future-sort dimensions, a generated
infinite diary, dependent Kpt source events or labelled orbit data. -/
theorem actual_prior_canonical_age_after_zero_critical_interval
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (upper : IntegerGraphSupport d ell → Nat)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hZero : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m = 0) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) = upper := by
  exact (integerGraphAgeCanonical_interval_eq_of_zero_critical_count
    E ell d b m c hZero).trans hPrior

#print axioms Kk.oldSupportCommonCapacity_insert_critical_exact
#print axioms Kk.oldSupportCommonCapacity_eq_add_criticalCount
#print axioms Kk.oldSupportCommonCapacity_lt_ell_of_safe
#print axioms Kk.originalCriticalCount_add_final_raw_eq_initial_of_safe
#print axioms Kk.originalCriticalCount_zero_iff_raw_eq_of_safe
#print axioms Kk.finiteOldColumnRawBound_interval_eq_of_zero_critical_count
#print axioms Kk.all_critical_count_zero_iff_raw_interval_eq_of_safe
#print axioms Kk.integerGraphAgeCanonical_interval_eq_of_zero_critical_count
#print axioms Kk.actual_prior_canonical_age_after_zero_critical_interval

end Kk
