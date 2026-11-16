import Kk.FullOriginalInsertionAge
import Mathlib.Tactic

/-!
# Track B: a real original changes each raw future support by zero or one

English proof and adversarial checks were written first in:
docs/track_b_critical_one_original_supports_english_audit.md

The exact original insertion recurrence sharpens to a dichotomy:
adding a FRESH vertex v raises a directed-clique capacity by one
iff v is mutually adjacent to SOME maximum old clique (equivalently
the mutual-neighbour clique capacity equals the old capacity).
Otherwise it does not raise it.

This classifies every literal old-column raw support change by a
finite intrinsic critical-support condition; it is NOT a theorem
that one original causes precisely one canonical graph-age cover,
nor a proof of the unbounded resolved copy or Kpt L+ events.
-/

namespace Kk

/-- A single FRESH vertex either leaves clique capacity unchanged
or raises it by EXACTLY one. Growth occurs iff its true MUTUAL
neighbour pool contains a maximum old directed clique. -/
theorem finiteDirectedCliqueCapacity_insert_one_jump
    (E : Nat → Nat → Bool) (X : Finset Nat) (v : Nat) (hv : v ∉ X) :
    finiteDirectedCliqueCapacity E (insert v X) =
      if finiteDirectedCliqueCapacity E (mutualLinkedNeighbours E X v) =
          finiteDirectedCliqueCapacity E X then
        finiteDirectedCliqueCapacity E X + 1
      else finiteDirectedCliqueCapacity E X := by
  classical
  have hSubset : mutualLinkedNeighbours E X v ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hLe : finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E X v) ≤
      finiteDirectedCliqueCapacity E X :=
    finiteDirectedCliqueCapacity_mono E _ _ hSubset
  rw [finiteDirectedCliqueCapacity_insert_eq E X v hv]
  by_cases hEq : finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E X v) =
        finiteDirectedCliqueCapacity E X
  · simp only [if_pos hEq]
    omega
  · simp only [if_neg hEq]
    omega

/-- The true original-vertex event which can increase clique
capacity at a supported future sort set U. The old pool contains
ALL original indices with positive future columns to EVERY sort
of U, not only selected or reserved names. -/
def originalCriticalSupport
    {d ell : Nat} (E : Nat → Nat → Bool)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) : Prop :=
  (∀ t ∈ U.1, c v t = true) ∧
    finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E
        (oldSupportCommonNeighbourPool P c U.1) v) =
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool P c U.1)

/-- Pointwise LITERAL raw-age update by a single fresh original:
subtract exactly one on a critical support, and change nothing
otherwise. NATURAL truncated subtraction is essential for raw zero
supports; the actual old prefix need not yet be forbidden-free. -/
theorem finiteOldColumnRawBound_insert_critical_exact
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P) :
    finiteOldColumnRawBound E ell d (insert v P) c U =
      (by
        classical
        -- This finite existential criticality predicate is Prop-valued;
        -- supply its classical Decidable instance ONLY for the RHS ite.
        exact if originalCriticalSupport E P c U v then
          finiteOldColumnRawBound E ell d P c U - 1
        else finiteOldColumnRawBound E ell d P c U) := by
  classical
  have hSubset : mutualLinkedNeighbours E
      (oldSupportCommonNeighbourPool P c U.1) v ⊆
      oldSupportCommonNeighbourPool P c U.1 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hLe : finiteDirectedCliqueCapacity E
      (mutualLinkedNeighbours E
        (oldSupportCommonNeighbourPool P c U.1) v) ≤
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool P c U.1) :=
    finiteDirectedCliqueCapacity_mono E _ _ hSubset
  -- Expose the classically decided RHS in the statement as an ordinary ite.
  -- This is definitional normalization, not a new theorem assumption.
  change
    finiteOldColumnRawBound E ell d (insert v P) c U =
      if originalCriticalSupport E P c U v then
        finiteOldColumnRawBound E ell d P c U - 1
      else finiteOldColumnRawBound E ell d P c U
  rw [finiteOldColumnRawBound_insert_exact E ell d P c U v hv]
  by_cases hLive : ∀ t ∈ U.1, c v t = true
  · simp only [if_pos hLive]
    by_cases hEq : finiteDirectedCliqueCapacity E
        (mutualLinkedNeighbours E
          (oldSupportCommonNeighbourPool P c U.1) v) =
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1)
    · have hCrit : originalCriticalSupport E P c U v :=
        ⟨hLive, hEq⟩
      simp only [if_pos hCrit]
      change ell - 1 -
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) =
        (ell - 1 -
          finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool P c U.1)) - 1
      omega
    · have hNotCrit : ¬ originalCriticalSupport E P c U v := by
        intro hc
        exact hEq hc.2
      simp only [if_neg hNotCrit]
      change ell - 1 -
        max (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1))
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool P c U.1) v)) =
        ell - 1 -
          finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool P c U.1)
      omega
  · have hNotCrit : ¬ originalCriticalSupport E P c U v := by
      intro hc
      exact hLive hc.1
    simp only [if_neg hLive, if_neg hNotCrit]
    rfl

/-- For an actually K_ell-free enlarged original pool, truncation
cannot hide the capacity increase of a critical support. The raw
support value STRICTLY drops iff this insertion is critical;
the decrease is exactly one by the previous theorem.

Do not infer the same iff for canonicalized graph-age values. -/
theorem finiteOldColumnRawBound_insert_strict_drop_iff_critical_of_safe
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (U : IntegerGraphSupport d ell) (v : Nat) (hv : v ∉ P)
    (hSafe : finitePoolCliqueCheck E ell (insert v P) = false) :
    (finiteOldColumnRawBound E ell d (insert v P) c U <
      finiteOldColumnRawBound E ell d P c U) ↔
      originalCriticalSupport E P c U v := by
  classical
  constructor
  · intro hDrop
    by_contra hNot
    rw [finiteOldColumnRawBound_insert_critical_exact
      E ell d P c U v hv, if_neg hNot] at hDrop
    exact (lt_irrefl _) hDrop
  · intro hCrit
    rw [finiteOldColumnRawBound_insert_critical_exact
      E ell d P c U v hv, if_pos hCrit]
    let X : Finset Nat := oldSupportCommonNeighbourPool P c U.1
    have hFresh : v ∉ X := by
      intro hIn
      exact hv (Finset.mem_filter.mp hIn).1
    have hNewSub : insert v X ⊆ insert v P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hEq | hOld
      · subst x
        exact Finset.mem_insert_self v P
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp hOld).1
    have hCapSub := finiteDirectedCliqueCapacity_mono E
      (insert v X) (insert v P) hNewSub
    have hFull :
        finiteDirectedCliqueCapacity E (insert v P) < ell :=
      (finitePoolCliqueCheck_false_iff_capacity_lt
        E ell (insert v P)).mp hSafe
    have hMax :
        finiteDirectedCliqueCapacity E (insert v X) =
          finiteDirectedCliqueCapacity E X + 1 := by
      rw [finiteDirectedCliqueCapacity_insert_one_jump E X v hFresh]
      have hEq : finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E X v) =
        finiteDirectedCliqueCapacity E X := hCrit.2
      simp only [hEq, if_true]
    have hPositive : 0 <
        finiteOldColumnRawBound E ell d P c U := by
      change 0 < ell - 1 - finiteDirectedCliqueCapacity E X
      rw [hMax] at hCapSub
      omega
    omega

#print axioms Kk.finiteDirectedCliqueCapacity_insert_one_jump
#print axioms Kk.originalCriticalSupport
#print axioms Kk.finiteOldColumnRawBound_insert_critical_exact
#print axioms Kk.finiteOldColumnRawBound_insert_strict_drop_iff_critical_of_safe

end Kk
