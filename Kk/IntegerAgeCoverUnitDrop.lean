import Kk.AutomaticAgeCoverChain
import Kk.IntegerAgeLocality
import Mathlib.Tactic

/-!
# A genuine graph-age cover drops by exactly one at every changed support

The English proof and adversarial audit were committed first in
`docs/track_b_automatic_cover_chain_english_audit_20261122.md`.

This is a finite normalized-integer-witness theorem; it does not assume a
special support nor import a blanket geometric or dependent Kpt axiom.
-/

namespace Kk

/-- Clipping a positive genuine age by one at a support has EXACTLY that
canonical value there. The proof decreases one positive coordinate of an
actual normalized saturated vector. -/
theorem integerGraphAgeCanonical_clip_pred_at
    (d ell : Nat)
    (upper : IntegerGraphSupport d ell → Nat)
    (hUpper : IsIntegerGraphAge d ell upper)
    (S : IntegerGraphSupport d ell) :
    integerGraphAgeCanonical d ell
      (integerAgeLowerAt d ell upper S (upper S - 1)) S =
      upper S - 1 := by
  classical
  obtain ⟨w, hw, hSat⟩ := hUpper.2 S
  have hPos : 0 < upper S := (hUpper.1 S).1
  have hChosen : ∃ j ∈ S.1, 0 < (w.1 j).val := by
    by_contra hNo
    push_neg at hNo
    have hZero : S.1.sum (fun t => (w.1 t).val) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hn := hNo t ht
      omega
    have hSat' : S.1.sum (fun t => (w.1 t).val) = upper S := hSat
    omega
  obtain ⟨j, hjS, hjPos⟩ := hChosen

  let down : Fin d → Fin ell := fun t =>
    ⟨(w.1 t).val - (if t = j then 1 else 0), by
      have ht : (w.1 t).val < ell := (w.1 t).isLt
      omega⟩
  have hPoint (t : Fin d) :
      (down t).val + (if t = j then 1 else 0) = (w.1 t).val := by
    change (w.1 t).val - (if t = j then 1 else 0) +
      (if t = j then 1 else 0) = (w.1 t).val
    by_cases ht : t = j
    · subst t
      simp only [ite_true]
      omega
    · simp [ht]
  have hCoord (t : Fin d) : (down t).val ≤ (w.1 t).val := by
    have ht := hPoint t
    omega
  have hWeightBound :
      (Finset.univ : Finset (Fin d)).sum (fun t => (down t).val) ≤
        (Finset.univ : Finset (Fin d)).sum
          (fun t => (w.1 t).val) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hCoord t
  let wDown : IntegerCliqueWeights d ell :=
    ⟨down, hWeightBound.trans w.2⟩

  have hIndicator : S.1.sum (fun t => if t = j then (1 : Nat) else 0) = 1 := by
    simp [Finset.sum_ite_eq', hjS]
  have hDropSum :
      S.1.sum (fun t => (down t).val) + 1 =
        S.1.sum (fun t => (w.1 t).val) := by
    calc
      _ = S.1.sum (fun t => (down t).val) +
          S.1.sum (fun t => if t = j then (1 : Nat) else 0) := by
            rw [hIndicator]
      _ = S.1.sum
          (fun t => (down t).val + (if t = j then 1 else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = S.1.sum (fun t => (w.1 t).val) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact hPoint t
  have hDownAt : integerCliqueOnSupport wDown S = upper S - 1 := by
    change S.1.sum (fun t => (down t).val) = upper S - 1
    have hSat' : S.1.sum (fun t => (w.1 t).val) = upper S := hSat
    omega

  have hRespectsUpper :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) upper wDown := by
    intro U
    calc
      integerCliqueOnSupport wDown U =
          U.1.sum (fun t => (down t).val) := rfl
      _ ≤ U.1.sum (fun t => (w.1 t).val) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hCoord t
      _ = integerCliqueOnSupport w U := rfl
      _ ≤ upper U := hw U
  let D := integerAgeLowerAt d ell upper S (upper S - 1)
  have hRespectsD :
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) D wDown := by
    intro U
    by_cases hUS : U = S
    · subst U
      have hOld := hRespectsUpper S
      have hNew : integerCliqueOnSupport wDown S ≤ upper S - 1 := by
        rw [hDownAt]
      simpa [D, integerAgeLowerAt] using
        (le_min hOld hNew)
    · simpa only [D, integerAgeLowerAt, if_neg hUS] using
        hRespectsUpper U
  have hCanonBelow : integerGraphAgeCanonical d ell D S ≤ upper S - 1 := by
    have hRaw := integerGraphAgeCanonical_le_raw d ell D S
    have hAt : D S ≤ upper S - 1 := by
      simpa [D, integerAgeLowerAt] using
        (Nat.min_le_right (upper S) (upper S - 1))
    omega
  have hCanonAbove : upper S - 1 ≤ integerGraphAgeCanonical d ell D S := by
    rw [← hDownAt]
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell)) D wDown hRespectsD S
  exact Nat.le_antisymm hCanonBelow hCanonAbove

/-- The raw one-unit clipping forces the genuine lower member of a cover.
The changed support need not be inclusion-minimal. -/
theorem integerGraphAge_cover_changed_support_unit_drop
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (S : IntegerGraphSupport d ell)
    (hChanged : lower S < upper S) :
    upper S = lower S + 1 := by
  classical
  let D := integerAgeLowerAt d ell upper S (upper S - 1)
  have hLowerBelow : AgeLe lower D := by
    intro U
    by_cases hUS : U = S
    · subst U
      have hLe := hCover.le S
      have hPred : lower S ≤ upper S - 1 := by omega
      simpa [D, integerAgeLowerAt] using
        (le_min hLe hPred)
    · simpa only [D, integerAgeLowerAt, if_neg hUS] using
        (hCover.le U)
  have hAge : IsIntegerGraphAge d ell (integerGraphAgeCanonical d ell D) :=
    integerGraphAgeCanonical_is_age d ell D lower
      hCover.lower_age hLowerBelow
  have hLowerCanon : AgeLe lower (integerGraphAgeCanonical d ell D) :=
    integerGraphAgeCanonical_greatest d ell D lower
      hCover.lower_age hLowerBelow
  have hCanonUpper : AgeLe (integerGraphAgeCanonical d ell D) upper := by
    intro U
    exact (integerGraphAgeCanonical_le_raw d ell D U).trans
      (integerAgeLowerAt_le d ell upper S (upper S - 1) U)
  have hNotUpper : integerGraphAgeCanonical d ell D ≠ upper := by
    intro hEq
    have hRaw := integerGraphAgeCanonical_le_raw d ell D S
    rw [hEq] at hRaw
    have hD : D S ≤ upper S - 1 := by
      simpa [D, integerAgeLowerAt] using
        (Nat.min_le_right (upper S) (upper S - 1))
    omega
  have hEqualsLower : integerGraphAgeCanonical d ell D = lower := by
    rcases hCover.no_intermediate (integerGraphAgeCanonical d ell D)
      hAge hLowerCanon hCanonUpper with h | h
    · exact h
    · exact False.elim (hNotUpper h)
  have hClip :
      integerGraphAgeCanonical d ell D S = upper S - 1 := by
    exact integerGraphAgeCanonical_clip_pred_at d ell upper
      hCover.upper_age S
  have hLowerAt : lower S = upper S - 1 := by
    calc
      lower S = integerGraphAgeCanonical d ell D S :=
        (congrFun hEqualsLower S).symm
      _ = upper S - 1 := hClip
  omega

/-- The canonical positive clique-block size for every changed
coordinate of a genuine cover is forced, never an extra arithmetic axiom. -/
theorem integerGraphAge_cover_changed_support_block_size
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (S : IntegerGraphSupport d ell)
    (hChanged : lower S < upper S) :
    let r := ell - 1 - lower S
    0 < r ∧ r < ell ∧ ell = lower S + r + 1 := by
  have hUnit :=
    integerGraphAge_cover_changed_support_unit_drop d ell
      lower upper hCover S hChanged
  have hBound : upper S ≤ ell - 1 := (hCover.upper_age.1 S).2
  have hPos : 1 ≤ lower S := (hCover.lower_age.1 S).1
  dsimp
  omega

#print axioms Kk.integerGraphAgeCanonical_clip_pred_at
#print axioms Kk.integerGraphAge_cover_changed_support_unit_drop
#print axioms Kk.integerGraphAge_cover_changed_support_block_size

end Kk
