import Kk.PartialNumericRawSupportEvents
import Kk.PartialNumericAgeMonotonicity
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track A: the actual numerical-H ordinary-L age is stable at late partial cuts

English proof and adversarial audit were committed FIRST:
  docs/partial_numeric_late_age_stability_english_audit.md

For fixed given later original TOP names, every actual old RAW
support age at a partial numerical-H cut g>=ell-1 is identical
to that at each later partial cut h<=k in the same original b
block. The verified exact raw-event iff requires a straddled
threshold p_U<ell-1, impossible when g>=ell-1.

Consequently the entire canonical integer graph age and feasible
normalized integer clique multiplicities also agree.

Crucial: only ordinary binary L and cuts g<=k are considered.
The full parameter-closed Kpt E/(I1)--(I3)/(B3) envelope may
change despite this ordinary-L age stability.
-/

namespace Kk

open SuccessorTree.V10

/-- A readable abbreviation for the TRUE raw old numerical-H
ordinary binary-L age at the literal numbered partial cut
before generation g of current original b. -/
noncomputable def finiteNumericHPartialActualRawAt
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k b g M : Nat) (j : Fin d → Nat) :
    IntegerGraphSupport d ell → Nat :=
  finiteOldColumnRawBound
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    ell d (Finset.range (hPosition k b g))
    (fun z t => (finiteNumericHL
      (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1))

/-- All raw support bounds at partial cuts g,h with
ell-1<=g<=h<=k are exactly equal (not merely monotone).
This is an equality on ALL nonempty admissible supports. -/
theorem finiteNumericH_partial_actual_raw_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLate : ell-1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPartialActualRawAt E ell k b h M j =
      finiteNumericHPartialActualRawAt E ell k b g M j := by
  classical
  funext U
  have hMonotone :
      finiteNumericHPartialActualRawAt E ell k b h M j U ≤
        finiteNumericHPartialActualRawAt E ell k b g M j U :=
    finiteNumericH_partial_actual_raw_age_antitone
      E ell k b M g h hgh j U
  have hNotStrict :
      ¬ finiteNumericHPartialActualRawAt E ell k b h M j U <
        finiteNumericHPartialActualRawAt E ell k b g M j U := by
    intro hStrict
    obtain ⟨_,_,hGLe,_,hBelow⟩ :=
      (finiteNumericH_partial_actual_raw_support_event_iff
        E hSym ell k b g h M hgh hh j hj U).mp hStrict
    omega
  omega

/-- The entire canonical integer graph age is stable once
the current b partial generation cut has reached ell-1.
No canonical COVER or (B3) source claim is inferred. -/
theorem finiteNumericH_partial_actual_canonical_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLate : ell-1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [finiteNumericH_partial_actual_raw_stable_after_ell_pred
    E hSym ell k b g h M hLate hgh hh j hj]

/-- The finite feasible normalized integer clique-vector family
has the same late-partial-cut stability. -/
theorem finiteNumericH_partial_actual_feasible_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLate : ell-1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [finiteNumericH_partial_actual_raw_stable_after_ell_pred
    E hSym ell k b g h M hLate hgh hh j hj]

#print axioms Kk.finiteNumericH_partial_actual_raw_stable_after_ell_pred
#print axioms Kk.finiteNumericH_partial_actual_canonical_stable_after_ell_pred
#print axioms Kk.finiteNumericH_partial_actual_feasible_stable_after_ell_pred

end Kk
