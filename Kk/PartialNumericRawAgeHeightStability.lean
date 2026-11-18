import Kk.PartialNumericCanonicalEventWitness
import Kk.PartialNumericRawSupportEvents
import Mathlib.Tactic

/-!
# Track A: ordinary numerical-H raw/canonical age freezes above ell-1

The English proof and fifteen hostile checks were committed
BEFORE Lean in
  docs/partial_numeric_raw_age_height_stability_english_audit.md

For the SAME original E and GIVEN later top-original names j,
every partial numbered H cut ell-1<=g<=h<=k has exactly
the same ordinary-L RAW old graph-age function. Therefore the
canonical integer graph age and feasible integer clique-vector
families are also identical. This uses the verified precise
physical raw event criterion: any strict raw decrease would need
g<=p_U<ell-1, contradicting ell-1<=g.

The non-top restriction h<=k is essential: at the next
completed original b+1 block, top-to-top H generation edges
are available and a different identity applies.

This is NOT a full parameter-closed Kpt E/(B3) stability
theorem and supplies no recursive original schedule or BRDs.
-/

namespace Kk

open SuccessorTree.V10

/-- For the same true numeric-H ordinary-L model and the same
given later top-original names, its ENTIRE old raw graph-age
function is independent of partial cut g after reaching ell-1,
until (but NOT including) the completed b top block. -/
theorem finiteNumericH_partial_raw_age_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLarge : ell - 1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPhysicalPartialOldRaw E ell k b h M j =
      finiteNumericHPhysicalPartialOldRaw E ell k b g M j := by
  classical
  funext U
  have hMono :
      finiteNumericHPhysicalPartialOldRaw E ell k b h M j U ≤
        finiteNumericHPhysicalPartialOldRaw E ell k b g M j U :=
    finiteNumericH_partial_actual_raw_age_antitone
      E ell k b M g h hgh j U
  have hNotStrict :
      ¬ finiteNumericHPhysicalPartialOldRaw E ell k b h M j U <
        finiteNumericHPhysicalPartialOldRaw E ell k b g M j U := by
    intro hEvent
    have hCriterion :=
      (finiteNumericH_partial_actual_raw_support_event_iff
        E hSym ell k b g h M hgh hh j hj U).mp hEvent
    omega
  omega

/-- Canonical normalized integer age is constant after generation
ell-1 within one original b partial block for the SAME future
original top family. Not a dependent auxiliary Kpt E/B3 event. -/
theorem finiteNumericH_partial_canonical_age_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLarge : ell - 1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b h M j) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b g M j) := by
  rw [finiteNumericH_partial_raw_age_stable_after_ell_pred
    E hSym ell k b g h M hLarge hgh hh j hj]

/-- All feasible normalized integer clique multiplicity vectors
remain identical at the late partial cuts g≥ell-1. -/
theorem finiteNumericH_partial_feasible_vectors_stable_after_ell_pred
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat)
    (hLarge : ell - 1 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b h M j) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b g M j) := by
  rw [finiteNumericH_partial_raw_age_stable_after_ell_pred
    E hSym ell k b g h M hLarge hgh hh j hj]

/-- In the manuscript's height k=ell convention, the
final TWO partial cuts before b's top block have the
SAME physical raw graph age. This does not preclude
a parameter-closed B3 or source-index event at either cut. -/
theorem finiteNumericH_partial_last_two_raw_cuts_equal
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell b M : Nat) (hEll : 1 ≤ ell)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    finiteNumericHPhysicalPartialOldRaw E ell ell b ell M j =
      finiteNumericHPhysicalPartialOldRaw E ell ell b (ell - 1) M j := by
  apply finiteNumericH_partial_raw_age_stable_after_ell_pred
    E hSym ell ell b (ell - 1) ell M
  · exact le_refl _
  · omega
  · exact le_refl _
  · exact j
  · exact hj

#print axioms Kk.finiteNumericH_partial_raw_age_stable_after_ell_pred
#print axioms Kk.finiteNumericH_partial_canonical_age_stable_after_ell_pred
#print axioms Kk.finiteNumericH_partial_feasible_vectors_stable_after_ell_pred
#print axioms Kk.finiteNumericH_partial_last_two_raw_cuts_equal

end Kk
