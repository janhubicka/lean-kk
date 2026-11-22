import Kk.FullOriginalInsertionAge
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Mathlib.Tactic

/-!
# Track B: exact all-support canonical age preservation across selected witnesses

English proof and 16 hostile checks FIRST in
docs/audits/2026-11-22-track-b-selected-witness-canonical-budget.md.

The actual original graph E and the entire full future-column table c are
fixed. The new finite old pool Q may contain arbitrary earlier selected
coding/top witnesses, with nonzero passing columns and arbitrary genuine
edges to old originals. No claim that the coherent resolved diary supplies
the budgets is made.

This is an exact age equivalence, not a new construction, global Kpt
source-orbit theorem, or full BRD characterization.
-/

namespace Kk

/-- All-support exact criterion for preserving a positive genuine
canonical age after adding an arbitrary finite family of actual originals.

The old column age is genuinely F, but its raw support bounds need not equal F.
Because P⊆Q, its new canonical age cannot increase. Equality holds iff
every old-common-neighbour clique capacity still fits the entire age F on
every admissible support. Positivity excludes the Nat subtraction trap. -/
theorem finiteOldColumnCanonical_eq_iff_full_witness_budget
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hPQ : P ⊆ Q)
    (c : Nat → Fin d → Bool)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hPositive : ∀ U : IntegerGraphSupport d ell, 1 ≤ F U)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) = F) :
    (integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d Q c) = F) ↔
      ∀ U : IntegerGraphSupport d ell,
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool Q c U.1) + F U ≤ ell - 1 := by
  classical
  let Bp : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d P c
  let Bq : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d Q c
  have hRawMono : AgeLe Bq Bp := by
    intro U
    exact finiteOldColumnRawBound_antitone_old_pool
      E ell d P Q c U hPQ
  have hUpper : AgeLe (integerGraphAgeCanonical d ell Bq) F := by
    intro U
    calc
      integerGraphAgeCanonical d ell Bq U ≤
          integerGraphAgeCanonical d ell Bp U :=
        integerGraphAgeCanonical_mono_raw d ell Bq Bp hRawMono U
      _ = F U := by
        simpa only [Bp] using congrArg (fun G => G U) hOld
  constructor
  · intro hEq U
    have hRaw := integerGraphAgeCanonical_le_raw d ell Bq U
    rw [hEq] at hRaw
    change F U ≤ ell - 1 -
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool Q c U.1) at hRaw
    have hPos := hPositive U
    omega
  · intro hBudget
    have hBelowRaw : AgeLe F Bq := by
      intro U
      change F U ≤ ell - 1 -
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool Q c U.1)
      have hBudgetU := hBudget U
      omega
    have hLower : AgeLe F (integerGraphAgeCanonical d ell Bq) :=
      integerGraphAgeCanonical_greatest d ell Bq F hAge hBelowRaw
    funext U
    exact Nat.le_antisymm (hUpper U) (hLower U)

/-- Same iff for an arbitrary finite family W of actual earlier
top/coding witness originals newly protected together with P.
No mutual nonedge or isolated-block assumption on W is inserted. -/
theorem finiteOldColumnCanonical_selectedWitnesses_iff_full_budget
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P W : Finset Nat) (c : Nat → Fin d → Bool)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hPositive : ∀ U : IntegerGraphSupport d ell, 1 ≤ F U)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) = F) :
    (integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (P ∪ W) c) = F) ↔
      ∀ U : IntegerGraphSupport d ell,
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (P ∪ W) c U.1) +
            F U ≤ ell - 1 := by
  exact finiteOldColumnCanonical_eq_iff_full_witness_budget
    E ell d P (P ∪ W) (Finset.subset_union_left) c F
    hAge hPositive hOld

#print axioms Kk.finiteOldColumnCanonical_eq_iff_full_witness_budget
#print axioms Kk.finiteOldColumnCanonical_selectedWitnesses_iff_full_budget

end Kk
