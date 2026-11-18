import Kk.PointedContinuationColumn
import Kk.FiniteOldColumnAge
import Mathlib.Tactic

/-!
# Track B: exact one-unit canonical loss from a tight actual clique

Section 5 of `docs/track_b_pointed_continuation_english_audit.md` was written
and independently audited before this module. Choose the pivot from an actual
clique attaining a tight old raw support bound. Deleting that pivot supplies
a simultaneous feasible witness for the explicitly constructed next column.
The surviving clique is used over the smaller old-plus-pivot pool, then the
raw-bound identity transfers it to the full protected prefix. It is not
mistakenly asserted to lie outside that full prefix.

The exact loss concerns one support coordinate; it is not an assertion of one
cover in the entire age order, or of any full Kpt/B3 transport.
-/

namespace Kk

/-- Removing the chosen pivot from an actual typed clique gives a lower bound
for the canonical age of the constructed pointed continuation. The old and
new support dimensions agree here; the pivot is positive precisely on T. -/
theorem pointedContinuation_canonical_ge_clique_pred
    (E : Nat → Nat → Bool) (d ell b v H : Nat)
    (c : Nat → Fin d → Bool) (sort : Nat → Fin d)
    (C : Finset Nat) (T : IntegerGraphSupport d ell)
    (hv : v ∈ C) (hvH : v < H)
    (hAfter : ∀ w ∈ C, b ≤ w)
    (hClique : IsDirectedCliqueOn E C)
    (hSort : ∀ w ∈ C, sort w ∈ T.1)
    (hColumns : ∀ p, p < b → ∀ w ∈ C,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hFree : finitePoolCliqueCheck E ell (Finset.range b ∪ C) = false) :
    C.card - 1 ≤
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range H)
          (pointedContinuationColumn b v c id
            (fun t => decide (t ∈ T.1)))) T := by
  classical
  let beta : Fin d → Bool := fun t => decide (t ∈ T.1)
  let cNext := pointedContinuationColumn b v c id beta
  let P : Finset Nat := insert v (Finset.range b)
  let R : Finset Nat := C.erase v
  have hbv : b ≤ v := hAfter v hv
  have hRSub : R ⊆ C := Finset.erase_subset _ _
  have hRClique : IsDirectedCliqueOn E R := by
    intro x hx y hy hxy
    exact hClique x (hRSub hx) y (hRSub hy) hxy
  have hDisjoint : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxR
    obtain ⟨hxv, hxC⟩ := Finset.mem_erase.mp hxR
    rcases Finset.mem_insert.mp hxP with hxEq | hxOld
    · exact hxv hxEq
    · have hxLt := Finset.mem_range.mp hxOld
      have hxGe := hAfter x hxC
      omega
  have hUnion : P ∪ R = Finset.range b ∪ C := by
    ext x
    by_cases hxv : x = v
    · subst x
      simp [P, R, hv]
    · simp [P, R, hxv]
  have hPSub : P ⊆ Finset.range b ∪ C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxv | hxOld
    · subst x
      exact Finset.mem_union.mpr (Or.inr hv)
    · exact Finset.mem_union.mpr (Or.inl hxOld)
  have hPFree : finitePoolCliqueCheck E ell P = false := by
    apply (finitePoolCliqueCheck_false_iff E ell P).mpr
    rintro ⟨D, hDSub, hDCard, hDClique⟩
    exact ((finitePoolCliqueCheck_false_iff E ell
      (Finset.range b ∪ C)).mp hFree)
      ⟨D, hDSub.trans hPSub, hDCard, hDClique⟩
  have hNextColumns : ∀ p ∈ P, ∀ w ∈ R,
      E p w = cNext p (sort w) ∧ E w p = cNext p (sort w) := by
    intro p hp w hw
    obtain ⟨hwv, hwC⟩ := Finset.mem_erase.mp hw
    rcases Finset.mem_insert.mp hp with hpv | hpOld
    · subst p
      have hBit : cNext v (sort w) = true := by
        dsimp [cNext]
        rw [pointedContinuationColumn_pivot b v c id beta hbv (sort w)]
        simp [beta, hSort w hwC]
      rw [hBit]
      exact ⟨hClique v hv w hwC (Ne.symm hwv), hClique w hwC v hv hwv⟩
    · have hpLt := Finset.mem_range.mp hpOld
      have hBit : cNext p (sort w) = c p (sort w) := by
        exact pointedContinuationColumn_old b v c id beta p hpLt (sort w)
      rw [hBit]
      exact hColumns p hpLt w hwC
  have hJoinedFree : finitePoolCliqueCheck E ell (P ∪ R) = false := by
    rw [hUnion]
    exact hFree
  have hBounds := ((finiteOldFuture_free_iff_canonical_support
    E ell d P R sort cNext hDisjoint hNextColumns hPFree).mp hJoinedFree).2
  have hLower := hBounds R (Finset.Subset.refl R) hRClique T
  have hFilter : R.filter (fun w => sort w ∈ T.1) = R := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact hSort w (hRSub hw)
  have hCard : R.card = C.card - 1 := Finset.card_erase_of_mem hv
  rw [hFilter, hCard] at hLower
  have hRaw := pointedContinuation_raw_eq_insert
    E ell b v H c id beta hbv hvH
  change C.card - 1 ≤ integerGraphAgeCanonical d ell
    (finiteOldColumnRawBound E ell d (Finset.range H) cNext) T
  rw [hRaw]
  exact hLower

/-- At a support containing the pivot's old sort, making the pivot positive
on that entire support decreases the literal raw bound by exactly one,
including truncated zero bounds and all real intervening originals. -/
theorem pointedContinuation_raw_on_pivot_support
    (E : Nat → Nat → Bool) (d ell b v H : Nat)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (T : IntegerGraphSupport d ell)
    (hbv : b ≤ v) (hvH : v < H) (hs : s ∈ T.1)
    (hColumn : ∀ p, p < b → E p v = c p s ∧ E v p = c p s) :
    finiteOldColumnRawBound E ell d (Finset.range H)
        (pointedContinuationColumn b v c id
          (fun t => decide (t ∈ T.1))) T =
      finiteOldColumnRawBound E ell d (Finset.range b) c T - 1 := by
  classical
  rw [pointedContinuation_raw_bound E ell b v H c s id
    (fun t => decide (t ∈ T.1)) hbv hvH hColumn]
  have hAll : ∀ t ∈ T.1, decide (t ∈ T.1) = true := by simp
  simp only [pointedContinuationRawBound, if_pos hAll,
    Finset.image_id, Finset.insert_eq_of_mem hs]
  unfold finiteOldColumnRawBound
  omega

/-- If an actual T-clique attains the old raw T-bound, choose the pivot from
that clique. The constructed continuation then has canonical T-value exactly
one less. Other coordinates may change too, and zero is allowed when the old
clique has one vertex. No existence of a next positive T-column is assumed. -/
theorem pointedContinuation_canonical_eq_clique_pred_of_raw_tight
    (E : Nat → Nat → Bool) (d ell b v H : Nat)
    (c : Nat → Fin d → Bool) (sort : Nat → Fin d)
    (C : Finset Nat) (T : IntegerGraphSupport d ell)
    (hv : v ∈ C) (hvH : v < H)
    (hAfter : ∀ w ∈ C, b ≤ w)
    (hClique : IsDirectedCliqueOn E C)
    (hSort : ∀ w ∈ C, sort w ∈ T.1)
    (hColumns : ∀ p, p < b → ∀ w ∈ C,
      E p w = c p (sort w) ∧ E w p = c p (sort w))
    (hFree : finitePoolCliqueCheck E ell (Finset.range b ∪ C) = false)
    (hTight : finiteOldColumnRawBound E ell d (Finset.range b) c T = C.card) :
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range H)
          (pointedContinuationColumn b v c id
            (fun t => decide (t ∈ T.1)))) T = C.card - 1 := by
  classical
  apply Nat.le_antisymm
  · have hUpper := integerGraphAgeCanonical_le_raw d ell
      (finiteOldColumnRawBound E ell d (Finset.range H)
        (pointedContinuationColumn b v c id
          (fun t => decide (t ∈ T.1)))) T
    have hRaw := pointedContinuation_raw_on_pivot_support E d ell b v H c
      (sort v) T (hAfter v hv) hvH (hSort v hv)
      (fun p hp => hColumns p hp v hv)
    rw [hRaw, hTight] at hUpper
    exact hUpper
  · exact pointedContinuation_canonical_ge_clique_pred
      E d ell b v H c sort C T hv hvH hAfter hClique hSort hColumns hFree

#print axioms Kk.pointedContinuation_canonical_ge_clique_pred
#print axioms Kk.pointedContinuation_raw_on_pivot_support
#print axioms Kk.pointedContinuation_canonical_eq_clique_pred_of_raw_tight

end Kk
