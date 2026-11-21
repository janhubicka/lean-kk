import Kk.ProspectiveControlledPreAge
import Kk.FiniteControlledNormalization
import Mathlib.Tactic

/-!
# A prospective finite event supplies its own controlled normalization

English first: `docs/track_b_controlled_preage_english_audit_20261121.md`
and `docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`.

The survivor age R is computed from the complete old columns and an abstract
pivot event. The controlled pre-age C is then explicitly constructed and
proved below the old raw age. Actual support blocks realize C before an
actual numerical pivot is chosen. Its post-age is exactly the prospective R
on all surviving supports, with all initial protected columns retained.

No C≤P, prepared-age equality, pointed budget, or actual pivot is supplied
as an input. Prescribed cover order and full dependent Kpt/B3 history remain
outside this finite ordinary-graph construction.
-/

namespace Kk

/-- Construct the full finite normalization for a prospective coding event.
Only the computed surviving sorts and old pivot singleton must be positive.
Every initial selected/reserved/parameter original is protected by the full
prefix. Numerical pivot selection follows, rather than precedes, preparation. -/
theorem henson_leftDense_normalizes_prospective_coding
    (E : Nat → Nat → Bool) (d e ell b N : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (hX : X ⊆ Finset.univ.erase j)
    (hSurvivors : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j →
      1 ≤ integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X) U)
    (hPivot : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hSurvivor : ∀ u, pi u ∈ Finset.univ.erase j)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    let R := integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X)
    let C := controlledPreAge R j X
    ∃ (F v : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧ F ≤ v ∧ N ≤ v ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' = C ∧
      (∀ p, p < v → E p v = delayedOldColumn F c' p j ∧
        E v p = delayedOldColumn F c' p j) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v)
          (delayedOldColumn F c')) = C ∧
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
          (protectedPivotColumn v
            (fun p u => delayedOldColumn F c' p (pi u)) beta)) =
        (fun U => R (integerGraphSupportImage pi U)) := by
  classical
  let R := integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X)
  let C := controlledPreAge R j X
  obtain ⟨hAge, hRawBelow, _, hCap, hGrowth⟩ :=
    prospective_controlledPreAge_is_age_and_below E d ell b hell
      c j X hX hSurvivors hPivot
  obtain ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext⟩ :=
    henson_leftDense_prepares_and_codes_controlled_age E d e ell b N hell
      hAvoid hDense c j C hAge hRawBelow X hCap hGrowth pi beta hPositive
  refine ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, ?_⟩
  rw [hNext]
  funext U
  apply controlledPreAge_survivor R j X
  intro t ht
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
  exact hSurvivor u

/-- The computed prospective event, its actual finite preparation, the late
pivot, and one common future stage share the same original columns. There is
one embedding and one numerical cutoff for every normalized clique profile. -/
theorem henson_leftDense_prospective_controlled_stage
    (E : Nat → Nat → Bool) (d e ell b N k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (hX : X ⊆ Finset.univ.erase j)
    (hSurvivors : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j →
      1 ≤ integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X) U)
    (hPivot : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hSurvivor : ∀ u, pi u ∈ Finset.univ.erase j)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    let R := integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X)
    let C := controlledPreAge R j X
    ∃ (F v : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧ F ≤ v ∧ N ≤ v ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' = C ∧
      (∀ p, p < v → E p v = delayedOldColumn F c' p j ∧
        E v p = delayedOldColumn F c' p j) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v)
          (delayedOldColumn F c')) = C ∧
      let Bcol := protectedPivotColumn v
        (fun p u => delayedOldColumn F c' p (pi u)) beta
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1)) Bcol) =
        (fun U => R (integerGraphSupportImage pi U)) ∧
      ∃ (f : Nat → Nat) (M : Nat),
        FiniteNumericStageWitness E e ell (v + 1) k he Bcol f M := by
  obtain ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext⟩ :=
    henson_leftDense_normalizes_prospective_coding E d e ell b N hell
      hAvoid hDense c j X hX hSurvivors hPivot pi beta hSurvivor hPositive
  refine ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext, ?_⟩
  exact henson_leftDense_finite_numeric_stage_witness E e ell (v + 1) k
    hell he hAvoid hDense
    (protectedPivotColumn v (fun p u => delayedOldColumn F c' p (pi u)) beta)

end Kk
