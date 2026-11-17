import Kk.OriginalCriticalSupport
import Mathlib.Tactic

/-!
# Track B: exact finite critical original count for every literal raw support

English mathematical proof and adversarial audit were committed first:
docs/track_b_critical_count_telescope_english_audit.md

For a fixed true directed original graph E and unchanged full typed future
column c, every actual original n has a critical-support indicator.
The literal raw age after a finite interval of original insertions is
the old raw age minus the TOTAL COUNT of critical original indices
(truncated subtraction), at EVERY nonempty supported future set U.

This does NOT identify canonical graph-age cover events, allow changed
sort dimensions without transport, construct a safe infinite schedule
or classify full Kpt dependent auxiliary L+ events and labelled orbits.
-/

namespace Kk

/-- The finite count of critical original insertions starting at b.
The primitive recursion runs over EVERY ORIGINAL index b+i, not only
a selected branch. Classical decidability is used only to
evaluate the finite Prop-valued criticality test. -/
noncomputable def originalCriticalCount
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (U : IntegerGraphSupport d ell)
    (m : Nat) : Nat := by
  classical
  exact Nat.rec 0
    (fun i previous =>
      previous +
        (if originalCriticalSupport E (Finset.range (b+i))
              c U (b+i) then 1 else 0))
    m

theorem originalCriticalCount_zero
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (U : IntegerGraphSupport d ell) :
    originalCriticalCount E ell d b c U 0 = 0 := by
  classical
  rfl

theorem originalCriticalCount_succ
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (U : IntegerGraphSupport d ell)
    (m : Nat) :
    originalCriticalCount E ell d b c U (m+1) =
      originalCriticalCount E ell d b c U m +
        (by
          classical
          exact if originalCriticalSupport E
            (Finset.range (b+m)) c U (b+m) then 1 else 0) := by
  classical
  rfl

/-- Exact finite telescope: one raw old-column support decreases by the
number of critical ACTUAL original insertions in [b,b+m), with
natural truncated subtraction. No K_ell-free/symmetry hypothesis
is needed for this purely directed raw-age identity.

A single original can be critical on several different supports;
the statement does not identify covers in the CANONICAL age poset. -/
theorem finiteOldColumnRawBound_eq_sub_criticalCount
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) :
    finiteOldColumnRawBound E ell d
      (Finset.range (b+m)) c U =
      finiteOldColumnRawBound E ell d (Finset.range b) c U -
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
      rw [finiteOldColumnRawBound_insert_critical_exact
        E ell d (Finset.range (b+m)) c U (b+m) hFresh]
      rw [originalCriticalCount_succ]
      by_cases hCritical :
          originalCriticalSupport E (Finset.range (b+m)) c U (b+m)
      · simp only [if_pos hCritical]
        rw [ih]
        omega
      · simp only [if_neg hCritical]
        simpa using ih

#print axioms Kk.originalCriticalCount
#print axioms Kk.originalCriticalCount_zero
#print axioms Kk.originalCriticalCount_succ
#print axioms Kk.finiteOldColumnRawBound_eq_sub_criticalCount

end Kk
