import Kk.IntegerAgeLocality
import Kk.IntegerAgeCoverSupport
import Mathlib.Tactic

/-!
# Track F: a genuine integer graph-age cover drops each value by ≤ 1

The finite integer-witness age axiom supplies a normalized clique vector
saturating any changed support. Decrementing one positive coordinate
preserves all upper support bounds and realizes the one-less total.
The canonical one-support restriction and the true cover relation then
force the lower age to have precisely that one-less value.

This is the manuscript's Lem:Consecutive(1), with no artificial axiom.
It does not yet prove part (3), non-free splitting, coded E bits,
or the full abstract/concrete diary correspondence.
-/

namespace Kk

/-- Decrease one positive coordinate *inside T* of a normalized
integer clique witness. Every subset clique count weakly decreases,
and the T-count falls by exactly one. -/
theorem trackF_integerWitness_drop_one
    (d ell : Nat)
    (w : IntegerCliqueWeights d ell)
    (T : IntegerGraphSupport d ell)
    (hPos : 0 < integerCliqueOnSupport w T) :
    ∃ w' : IntegerCliqueWeights d ell,
      (∀ U : IntegerGraphSupport d ell,
        integerCliqueOnSupport w' U ≤ integerCliqueOnSupport w U) ∧
      integerCliqueOnSupport w' T + 1 =
        integerCliqueOnSupport w T := by
  classical
  have hExists : ∃ x ∈ T.1, 0 < (w.1 x).val := by
    by_contra hNone
    have hZero : ∀ x ∈ T.1, (w.1 x).val = 0 := by
      intro x hx
      by_contra hNe
      have hxPos : 0 < (w.1 x).val := Nat.pos_of_ne_zero hNe
      exact hNone ⟨x, hx, hxPos⟩
    have hSumZero : integerCliqueOnSupport w T = 0 := by
      unfold integerCliqueOnSupport
      exact Finset.sum_eq_zero hZero
    omega
  obtain ⟨x,hx,hxPos⟩ := hExists
  let wFin : Fin d → Fin ell := fun j =>
    ⟨if j = x then (w.1 j).val - 1 else (w.1 j).val, by
      split_ifs with h
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (w.1 j).isLt
      · exact (w.1 j).isLt⟩
  have hPoint : ∀ j : Fin d, (wFin j).val ≤ (w.1 j).val := by
    intro j
    by_cases hj : j = x
    · simp [wFin, hj]
    · simp [wFin, hj]
  have hTotal :
      Finset.univ.sum (fun j : Fin d => (wFin j).val) ≤ ell - 1 := by
    calc
      _ ≤ Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
        apply Finset.sum_le_sum
        intro j _
        exact hPoint j
      _ ≤ ell - 1 := w.2
  let w' : IntegerCliqueWeights d ell := ⟨wFin,hTotal⟩
  have hOff : ∀ j : Fin d, j ≠ x →
      (wFin j).val = (w.1 j).val := by
    intro j hNe
    simp [wFin,hNe]
  have hErase :
      (T.1.erase x).sum (fun j => (wFin j).val) =
      (T.1.erase x).sum (fun j => (w.1 j).val) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hOff j (Finset.ne_of_mem_erase hj)
  have hAt : (wFin x).val + 1 = (w.1 x).val := by
    simp [wFin]
    omega
  have hOldSum :
      (T.1.erase x).sum (fun j => (w.1 j).val) +
        (w.1 x).val =
      T.1.sum (fun j => (w.1 j).val) :=
    T.1.sum_erase_add x hx
  have hNewSum :
      (T.1.erase x).sum (fun j => (wFin j).val) +
        (wFin x).val =
      T.1.sum (fun j => (wFin j).val) :=
    T.1.sum_erase_add x hx
  refine ⟨w', ?_, ?_⟩
  · intro U
    unfold integerCliqueOnSupport
    apply Finset.sum_le_sum
    intro j _
    exact hPoint j
  · change T.1.sum (fun j => (wFin j).val) + 1 =
        T.1.sum (fun j => (w.1 j).val)
    omega

/-- At every strictly changed support T of a genuine cover, the
integer graph-age value drops by **exactly one**. This uses
canonical maximality over a raw one-support restriction and an
actual decremented normalized feasible clique witness. -/
theorem trackFCover_drop_one_at_changed
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell)
    (hChanged : lower T < upper T) :
    upper T = lower T + 1 := by
  classical
  let n := upper T - 1
  let B := integerAgeLowerAt d ell upper T n
  have hLowerB : AgeLe lower B := by
    intro U
    by_cases hUT : U = T
    · subst U
      have hN : lower T ≤ n := by
        dsimp [n]
        omega
      simpa [B, integerAgeLowerAt] using
        (le_min (hCover.le T) hN)
    · simpa [B, integerAgeLowerAt, hUT] using hCover.le U
  have hHAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_is_age d ell B lower
      hCover.lower_age hLowerB
  have hLH : AgeLe lower (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_greatest d ell B lower
      hCover.lower_age hLowerB
  have hHU : AgeLe (integerGraphAgeCanonical d ell B) upper := by
    intro U
    exact (integerGraphAgeCanonical_le_raw d ell B U).trans
      (integerAgeLowerAt_le d ell upper T n U)
  have hNotUpper :
      integerGraphAgeCanonical d ell B ≠ upper := by
    intro hEq
    have hBound : upper T ≤ B T := by
      simpa only [hEq] using
        (integerGraphAgeCanonical_le_raw d ell B T)
    have hUpperLE : upper T ≤ n := by
      simpa [B, integerAgeLowerAt] using
        hBound.trans (Nat.min_le_right (upper T) n)
    dsimp [n] at hUpperLE
    have hPos : 0 < upper T := by omega
    omega
  have hHL :
      integerGraphAgeCanonical d ell B = lower := by
    rcases hCover.no_intermediate (integerGraphAgeCanonical d ell B)
        hHAge hLH hHU with h | h
    · exact h
    · exact False.elim (hNotUpper h)
  obtain ⟨w,hValid,hValue⟩ := hCover.upper_age.2 T
  have hValPos : 0 < integerCliqueOnSupport w T := by
    rw [hValue]
    omega
  obtain ⟨w',hSmaller,hDrop⟩ :=
    trackF_integerWitness_drop_one d ell w T hValPos
  have hW'B :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w' := by
    intro U
    have hUp : integerCliqueOnSupport w' U ≤ upper U :=
      (hSmaller U).trans (hValid U)
    by_cases hUT : U = T
    · subst U
      have hN : integerCliqueOnSupport w' T ≤ n := by
        dsimp [n]
        rw [hValue] at hDrop
        omega
      simpa [B, integerAgeLowerAt] using (le_min hUp hN)
    · simpa [B, integerAgeLowerAt, hUT] using hUp
  have hNLe : integerCliqueOnSupport w' T ≤
      integerGraphAgeCanonical d ell B T :=
    witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell)) B
      w' hW'B T
  have hLowerBound : n ≤ lower T := by
    rw [hHL] at hNLe
    rw [hValue] at hDrop
    dsimp [n]
    omega
  dsimp [n] at hLowerBound
  omega

/-- Part (1) of the manuscript's graph-age cover lemma: *every*
coordinate drops by at most one, with strict changes exactly one. -/
theorem trackFCover_drop_at_most_one
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (T : IntegerGraphSupport d ell) :
    upper T ≤ lower T + 1 := by
  by_cases hChanged : lower T < upper T
  · rw [trackFCover_drop_one_at_changed d ell lower upper
      hCover T hChanged]
  · have hLE := hCover.le T
    omega

end Kk
