import Kk.IntegerAgeCoverSupport
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track F: exact raw age-change columns for abstract K_ell diaries

If F' ⋖ F is a genuine cover of normalized integer-witness graph ages,
then an age-change column which lowers the raw bound on ALL nonempty
supports U ⊆ T to F'(T) canonicalizes to EXACTLY F'.

Only the abstract finite graph-age operations are involved here.
This module does not supply full abstract/concrete diary equivalence,
controlled coding, terminal labels, or an independent BRD lower bound.
-/

namespace Kk

/-- The raw bound read from a concrete age-change column with the new
positive symbol on precisely the active branches in T. -/
def diaryCoverColumnRaw
    (d ell : Nat) (upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) (n : Nat) :
    IntegerGraphSupport d ell → Nat :=
  fun U => if U.1 ⊆ T.1 then min (upper U) n else upper U

/-- A concrete age-change column only adds raw restrictions. -/
theorem diaryCoverColumnRaw_le_upper
    (d ell : Nat) (upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) (n : Nat) :
    AgeLe (diaryCoverColumnRaw d ell upper T n) upper := by
  classical
  intro U
  by_cases hUT : U.1 ⊆ T.1
  · simpa [diaryCoverColumnRaw, hUT] using
      (Nat.min_le_left (upper U) n)
  · simp [diaryCoverColumnRaw, hUT]

/-- The full raw column recreates the lower age exactly. A CHANGED
coordinate T suffices; uniqueness of the inclusion-minimal changed
coordinate, needed for diary event identification, is a separate lemma. -/
theorem diaryCoverColumnCanonical_exact
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hChanged : lower T < upper T) :
    integerGraphAgeCanonical d ell
      (diaryCoverColumnRaw d ell upper T (lower T)) = lower := by
  classical
  let B : IntegerGraphSupport d ell → Nat :=
    diaryCoverColumnRaw d ell upper T (lower T)
  have hLowerB : AgeLe lower B := by
    intro U
    by_cases hUT : U.1 ⊆ T.1
    · have hMon := integerGraphAge_monotone d ell
        lower hCover.lower_age U T hUT
      simpa [B, diaryCoverColumnRaw, hUT] using
        (le_min (hCover.le U) hMon)
    · simpa [B, diaryCoverColumnRaw, hUT] using hCover.le U
  have hBUpper : AgeLe B upper :=
    diaryCoverColumnRaw_le_upper d ell upper T (lower T)
  have hCanonicalAge :
      IsIntegerGraphAge d ell (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_is_age d ell B lower
      hCover.lower_age hLowerB
  have hLowerCanonical : AgeLe lower
      (integerGraphAgeCanonical d ell B) :=
    integerGraphAgeCanonical_greatest d ell B lower
      hCover.lower_age hLowerB
  have hCanonicalUpper : AgeLe
      (integerGraphAgeCanonical d ell B) upper := by
    intro U
    exact (integerGraphAgeCanonical_le_raw d ell B U).trans
      (hBUpper U)
  have hBT : B T = lower T := by
    simp [B, diaryCoverColumnRaw,
      Nat.min_eq_right (Nat.le_of_lt hChanged)]
  have hNotUpper :
      integerGraphAgeCanonical d ell B ≠ upper := by
    intro hEq
    have hBound : upper T ≤ B T := by
      simpa [hEq] using
        (integerGraphAgeCanonical_le_raw d ell B T)
    rw [hBT] at hBound
    omega
  rcases hCover.no_intermediate (integerGraphAgeCanonical d ell B)
      hCanonicalAge hLowerCanonical hCanonicalUpper with h | h
  · exact h
  · exact False.elim (hNotUpper h)

/-- The concrete age-change column and the true lower age admit
exactly the same normalized labelled clique multiplicity vectors. -/
theorem diaryCoverColumn_feasible_iff_lower
    (d ell : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hChanged : lower T < upper T)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (diaryCoverColumnRaw d ell upper T (lower T)) w ↔
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        lower w := by
  calc
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell
            (diaryCoverColumnRaw d ell upper T (lower T))) w :=
        (integerGraphAgeCanonical_preserves_clique_vectors d ell _ w).symm
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          lower w := by
        rw [diaryCoverColumnCanonical_exact d ell
          lower upper T hCover hChanged]

end Kk
