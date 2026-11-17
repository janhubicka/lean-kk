import Kk.OriginalCriticalCount
import Mathlib.Tactic

/-!
# Track B: genuine K_ell-free final prefixes detect EVERY critical old-original event

English proof and adversarial audit committed first:
docs/track_b_critical_neutral_cover_english_audit.md

The previously checked critical-count identity uses natural truncated
subtraction. A genuinely K_ell-free final old ORIGINAL prefix makes
every raw common-old-neighbour clique capacity < ell. Therefore the
final raw bound on any nonempty support is strictly positive and
truncation CANNOT hide an additional critical original.

This yields the exact nontruncated conservation identity:
  initial raw age = number of critical originals + final raw age.

Zero critical counts on ALL actual supports suffice to preserve the
whole raw and canonical reference ages over any FINITE original interval.
The result does NOT say that the canonical diary constructs such a
neutral interval or that full dependent Kpt L+ events are matched.
-/

namespace Kk

/-- A genuinely K_ell-free FINAL old original prefix has positive
raw continuation age at EVERY admissible nonempty support. This
uses the full physical old carrier, not the selected-front shadow. -/
theorem finiteOldColumnRawBound_final_positive_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    0 < finiteOldColumnRawBound E ell d
      (Finset.range (b+m)) c U := by
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
  change 0 < ell - 1 -
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range (b+m)) c U.1)
  omega

/-- Genuine final physical K_ell-freeness removes the truncation
ambiguity in the verified exact raw-age telescope.

The number of truly critical ORIGINAL insertions, plus final raw age,
is exactly the earlier raw age. All old gaps and parameter originals
are counted because the interval traverses the actual index order. -/
theorem originalCriticalCount_add_final_raw_eq_initial_of_safe
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell)
    (hSafe : finitePoolCliqueCheck E ell (Finset.range (b+m)) = false) :
    originalCriticalCount E ell d b c U m +
      finiteOldColumnRawBound E ell d (Finset.range (b+m)) c U =
      finiteOldColumnRawBound E ell d (Finset.range b) c U := by
  have hTel := finiteOldColumnRawBound_eq_sub_criticalCount
    E ell d b m c U
  have hPos := finiteOldColumnRawBound_final_positive_of_safe
    E ell d b m c U hSafe
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

#print axioms Kk.finiteOldColumnRawBound_final_positive_of_safe
#print axioms Kk.originalCriticalCount_add_final_raw_eq_initial_of_safe
#print axioms Kk.originalCriticalCount_zero_iff_raw_eq_of_safe
#print axioms Kk.finiteOldColumnRawBound_interval_eq_of_zero_critical_count
#print axioms Kk.all_critical_count_zero_iff_raw_interval_eq_of_safe
#print axioms Kk.integerGraphAgeCanonical_interval_eq_of_zero_critical_count
#print axioms Kk.actual_prior_canonical_age_after_zero_critical_interval

end Kk
