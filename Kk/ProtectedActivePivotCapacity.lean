import Kk.PhysicalPointedContinuation
import Kk.FullOriginalInsertionAge
import Mathlib.Tactic

/-!
Track B: arbitrarily nonzero protected passing columns with one pivot.
English proof and adversarial audit were committed before this source in
docs/track_b_protected_active_pointed_english_audit.md.
No full auxiliary Kpt source transport or global resolved copy is asserted.
-/
namespace Kk

def protectedPivotColumn {e : Nat} (v : Nat)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool) :
    Nat → Fin e → Bool :=
  fun p u => if p = v then beta u else a p u

def activeGapPointedColumn {d e : Nat} (b v : Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool) :
    Nat → Fin e → Bool :=
  fun p u => if p < b then c p (pi u)
    else if p = v then beta u else gap p u

theorem activeGapPointedColumn_old {d e : Nat} (b v : Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool)
    (p : Nat) (hp : p < b) (u : Fin e) :
    activeGapPointedColumn b v c pi beta gap p u = c p (pi u) := by
  simp [activeGapPointedColumn, hp]

theorem activeGapPointedColumn_pivot {d e : Nat} (b v : Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool)
    (hbv : b ≤ v) (u : Fin e) :
    activeGapPointedColumn b v c pi beta gap v u = beta u := by
  simp [activeGapPointedColumn, Nat.not_lt.mpr hbv]

theorem activeGapPointedColumn_gap {d e : Nat} (b v : Nat)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool)
    (p : Nat) (hbp : b ≤ p) (hpv : p ≠ v) (u : Fin e) :
    activeGapPointedColumn b v c pi beta gap p u = gap p u := by
  simp [activeGapPointedColumn, Nat.not_lt.mpr hbp, hpv]

/-- Every protected original remains in the actual prefix and retains
its arbitrary complete typed background column, including nonzero bits. -/
theorem protectedPivot_common_pool {e : Nat}
    (v H : Nat) (hvH : v < H)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool)
    (U : Finset (Fin e)) :
    oldSupportCommonNeighbourPool (Finset.range H)
      (protectedPivotColumn v a beta) U =
    if ∀ u ∈ U, beta u = true then
      insert v (oldSupportCommonNeighbourPool
        ((Finset.range H).erase v) a U)
    else oldSupportCommonNeighbourPool
        ((Finset.range H).erase v) a U := by
  classical
  let P := (Finset.range H).erase v
  have hRange : insert v P = Finset.range H := by
    exact Finset.insert_erase (Finset.mem_range.mpr hvH)
  have hBase :
      oldSupportCommonNeighbourPool P (protectedPivotColumn v a beta) U =
      oldSupportCommonNeighbourPool P a U := by
    ext p
    by_cases hpv : p = v
    · subst p
      simp [oldSupportCommonNeighbourPool, P]
    · simp [oldSupportCommonNeighbourPool, protectedPivotColumn, hpv]
  calc
    oldSupportCommonNeighbourPool (Finset.range H)
        (protectedPivotColumn v a beta) U =
      oldSupportCommonNeighbourPool (insert v P)
        (protectedPivotColumn v a beta) U := by rw [hRange]
    _ = if ∀ u ∈ U, beta u = true then
          insert v (oldSupportCommonNeighbourPool P a U)
        else oldSupportCommonNeighbourPool P a U := by
          rw [oldSupportCommonNeighbourPool_insert_exact]
          simp only [protectedPivotColumn, if_pos rfl]
          rw [hBase]

theorem protectedPivot_capacity {e : Nat}
    (E : Nat → Nat → Bool) (v H : Nat) (hvH : v < H)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool)
    (U : Finset (Fin e)) :
    let X := oldSupportCommonNeighbourPool
      ((Finset.range H).erase v) a U
    finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range H)
        (protectedPivotColumn v a beta) U) =
    if ∀ u ∈ U, beta u = true then
      max (finiteDirectedCliqueCapacity E X)
          (1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E X v))
    else finiteDirectedCliqueCapacity E X := by
  classical
  dsimp only
  rw [protectedPivot_common_pool v H hvH a beta U]
  split_ifs with hPositive
  · have hvNot : v ∉
        oldSupportCommonNeighbourPool
          ((Finset.range H).erase v) a U := by
      intro h
      have hm := (Finset.mem_filter.mp h).1
      exact (Finset.mem_erase.mp hm).1 rfl
    exact finiteDirectedCliqueCapacity_insert_eq E _ v hvNot
  · rfl

noncomputable def protectedPivotRaw {e : Nat}
    (E : Nat → Nat → Bool) (ell v H : Nat)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool) :
    IntegerGraphSupport e ell → Nat :=
  fun U => ell - 1 -
    (if ∀ u ∈ U.1, beta u = true then
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool
          ((Finset.range H).erase v) a U.1))
        (1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool
              ((Finset.range H).erase v) a U.1) v))
    else finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool
        ((Finset.range H).erase v) a U.1))

theorem protectedPivotRaw_eq_actual {e : Nat}
    (E : Nat → Nat → Bool) (ell v H : Nat) (hvH : v < H)
    (a : Nat → Fin e → Bool) (beta : Fin e → Bool) :
    finiteOldColumnRawBound E ell e (Finset.range H)
      (protectedPivotColumn v a beta) =
    protectedPivotRaw E ell v H a beta := by
  funext U
  unfold finiteOldColumnRawBound protectedPivotRaw
  rw [protectedPivot_capacity E v H hvH a beta U.1]

theorem activeGapPointedColumn_eq_protectedPivot {d e : Nat}
    (b v : Nat) (hbv : b ≤ v)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool) :
    activeGapPointedColumn b v c pi beta gap =
    protectedPivotColumn v
      (fun p u => if p < b then c p (pi u) else gap p u) beta := by
  funext p u
  by_cases hp : p < b
  · have hpv : p ≠ v := by omega
    simp [activeGapPointedColumn, protectedPivotColumn, hp, hpv]
  · by_cases hpv : p = v
    · subst p
      simp [activeGapPointedColumn, protectedPivotColumn, Nat.not_lt.mpr hbv]
    · simp [activeGapPointedColumn, protectedPivotColumn, hp, hpv]

theorem activeGapPointedRaw_eq_actual {d e : Nat}
    (E : Nat → Nat → Bool) (ell b v H : Nat)
    (hbv : b ≤ v) (hvH : v < H)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d)
    (beta : Fin e → Bool) (gap : Nat → Fin e → Bool) :
    finiteOldColumnRawBound E ell e (Finset.range H)
      (activeGapPointedColumn b v c pi beta gap) =
    protectedPivotRaw E ell v H
      (fun p u => if p < b then c p (pi u) else gap p u) beta := by
  rw [activeGapPointedColumn_eq_protectedPivot b v hbv c pi beta gap]
  exact protectedPivotRaw_eq_actual E ell v H hvH _ beta

#print axioms Kk.protectedPivot_common_pool
#print axioms Kk.protectedPivot_capacity
#print axioms Kk.protectedPivotRaw_eq_actual
#print axioms Kk.activeGapPointedRaw_eq_actual

end Kk
