import Kk.ProtectedActivePivotCapacity
import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# Exact active-pivot preservation criterion for arbitrary genuine target ages

English proof and adversarial audit were committed BEFORE this module:
docs/track_b_protected_pivot_age_budget_english_audit.md.

A genuine target integer graph age F is preserved below the full
new canonical graph age exactly when BOTH actual clique capacity
budgets hold for every admissible support U. All nonpivot original
passing columns can be arbitrary and nonzero. F(U)>=1 is essential
to convert truncated subtraction into addition inequalities.

No full dependent Kpt source or global BRD is asserted.
-/
namespace Kk

theorem protectedPivot_targetAge_le_canonical_iff_budgets {e : Nat}
    (E : Nat → Nat → Bool) (ell v H : Nat) (hvH : v < H)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool)
    (F : IntegerGraphSupport e ell → Nat)
    (hAge : IsIntegerGraphAge e ell F) :
    AgeLe F
      (integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range H)
          (protectedPivotColumn v a beta))) ↔
    ∀ U : IntegerGraphSupport e ell,
      let X := oldSupportCommonNeighbourPool
        ((Finset.range H).erase v) a U.1
      finiteDirectedCliqueCapacity E X + F U ≤ ell - 1 ∧
        ((∀ u ∈ U.1, beta u = true) →
          1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E X v) + F U ≤ ell - 1) := by
  classical
  rw [protectedPivotRaw_eq_actual E ell v H hvH a beta]
  constructor
  · intro hCan U
    dsimp only
    have hPos : 1 ≤ F U := (hAge.1 U).1
    have hRaw : F U ≤ protectedPivotRaw E ell v H a beta U :=
      (hCan U).trans
        ((integerGraphAgeCanonical_le_raw e ell
            (protectedPivotRaw E ell v H a beta)) U)
    unfold protectedPivotRaw at hRaw
    by_cases hLive : ∀ u ∈ U.1, beta u = true
    · simp only [if_pos hLive] at hRaw
      have hL := le_max_left
        (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool ((Finset.range H).erase v) a U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool ((Finset.range H).erase v) a U.1) v))
      have hR := le_max_right
        (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool ((Finset.range H).erase v) a U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool ((Finset.range H).erase v) a U.1) v))
      constructor
      · omega
      · intro _
        omega
    · simp only [if_neg hLive] at hRaw
      constructor
      · omega
      · intro h
        exact False.elim (hLive h)
  · intro hBudget
    apply integerGraphAgeCanonical_greatest e ell
      (protectedPivotRaw E ell v H a beta) F hAge
    intro U
    have h := hBudget U
    dsimp only at h
    unfold protectedPivotRaw
    by_cases hLive : ∀ u ∈ U.1, beta u = true
    · simp only [if_pos hLive]
      have hL := h.1
      have hR := h.2 hLive
      have hMax :
          max (finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool ((Finset.range H).erase v) a U.1))
            (1 + finiteDirectedCliqueCapacity E
              (mutualLinkedNeighbours E
                (oldSupportCommonNeighbourPool
                  ((Finset.range H).erase v) a U.1) v))
            ≤ ell - 1 - F U := by
        apply max_le
        · omega
        · omega
      omega
    · simp only [if_neg hLive]
      have hL := h.1
      omega

#print axioms Kk.protectedPivot_targetAge_le_canonical_iff_budgets

end Kk
