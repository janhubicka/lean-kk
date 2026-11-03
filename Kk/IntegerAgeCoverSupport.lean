import Kk.IntegerAgeLocality
import Mathlib.Tactic

/-!
# Minimal changed supports of a graph-age cover

The manuscript states that a genuine cover of graph ages has a unique
inclusion-minimal support on which its value changes. This is more
delicate than pointwise arithmetic: lowering an age bound on a set
can affect other overlapping sets through canonicalization.

The theorem below excludes two distinct minimal changed supports.
It uses the actual finite integer-witness canonicalizer and the
single-support locality theorem, not an assumed cover classification.
Existence of a minimal changed support follows separately from
finiteness of the support family. No statement about the complete
parameter-closed B3 test or labelled diary geometry is made.
-/

namespace Kk

/-- Two distinct inclusion-minimal changed supports cannot occur in
a cover of genuine integer-witness graph ages. The minimality
hypotheses state exactly that no *proper nonempty* support changes. -/
theorem integerGraphAgeCover_minimal_changed_unique
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (S T : IntegerGraphSupport d ell)
    (hSChanged : lower S < upper S)
    (hTChanged : lower T < upper T)
    (hMinS : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ S.1 → U.1 ≠ S.1 → lower U = upper U)
    (hMinT : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U) :
    S = T := by
  classical
  by_contra hNe
  have hSnotT : ¬ S.1 ⊆ T.1 := by
    intro hSub
    have hSetsNe : S.1 ≠ T.1 := by
      intro hEq
      exact hNe (Subtype.ext hEq)
    have hSame : lower S = upper S := hMinT S hSub hSetsNe
    omega
  have hOverlap : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ S.1 → U.1 ⊆ T.1 → upper U ≤ lower S := by
    intro U hUS hUT
    have hUNe : U.1 ≠ S.1 := by
      intro hEq
      apply hSnotT
      simpa only [hEq] using hUT
    have hSame : lower U = upper U := hMinS U hUS hUNe
    calc
      upper U = lower U := hSame.symm
      _ ≤ lower S :=
        integerGraphAge_monotone d ell lower hCover.lower_age U S hUS
  let B := integerAgeLowerAt d ell upper S (lower S)
  let G := integerGraphAgeCanonical d ell B
  have hLowerB : AgeLe lower B := by
    intro U
    by_cases hUS : U = S
    · subst U
      simpa [B, integerAgeLowerAt] using
        (le_min (hCover.le S) (le_refl _))
    · simpa [B, integerAgeLowerAt, hUS] using (hCover.le U)
  have hGage : IsIntegerGraphAge d ell G :=
    integerGraphAgeCanonical_is_age d ell B lower
      hCover.lower_age hLowerB
  have hLowerG : AgeLe lower G :=
    integerGraphAgeCanonical_greatest d ell B lower
      hCover.lower_age hLowerB
  have hGUpper : AgeLe G upper := by
    intro U
    exact (integerGraphAgeCanonical_le_raw d ell B U).trans
      (integerAgeLowerAt_le d ell upper S (lower S) U)
  have hGnotUpper : G ≠ upper := by
    intro hEq
    have hBound : G S ≤ B S :=
      integerGraphAgeCanonical_le_raw d ell B S
    rw [hEq] at hBound
    have hBound' : upper S ≤ min (upper S) (lower S) := by
      simpa [B, integerAgeLowerAt] using hBound
    have hContr : upper S ≤ lower S :=
      hBound'.trans (Nat.min_le_right _ _)
    omega
  have hGLower : G = lower := by
    rcases hCover.no_intermediate G hGage hLowerG hGUpper with h | h
    · exact h
    · exact False.elim (hGnotUpper h)
  have hTValue : G T = upper T :=
    integerGraphAgeCanonical_single_bound_locality
      d ell hell upper hCover.upper_age S T (lower S) hOverlap
  have hImpossible : lower T = upper T := by
    simpa only [hGLower] using hTValue
  omega

end Kk
