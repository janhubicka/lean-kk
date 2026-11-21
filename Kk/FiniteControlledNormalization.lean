import Kk.FiniteTargetAgeNormalization
import Kk.LateControlledPivot
import Mathlib.Tactic

/-!
# Prepare a finite controlled age, then choose and code its actual pivot

The English proof and independent audits preceded this source in
`docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`.

The target age is only assumed BELOW the original raw bound, not already
equal to an actual pre-age. Finite isolated support blocks construct that
equality while retaining every old column. Only then is the numerical pivot
chosen, after any requested cutoff. Its chronological pre-age and full
controlled post-age are conclusions of the same construction.

Intermediate drops need not be a prescribed saturated-cover diary. No full
dependent Kpt/history invariant or common labelled inverse orbit is claimed.
-/

namespace Kk

/-- Finite controlled normalization and coding in the unchanged Henson
graph, with every column on the original protected prefix retained. The
numerical pivot is constructed AFTER normalization, not fixed beforehand. -/
theorem henson_leftDense_prepares_and_codes_controlled_age
    (E : Nat → Nat → Bool) (d e ell b N : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (C : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell C)
    (hBelow : AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c))
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → C U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → C V = C U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    ∃ (F v : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧ F ≤ v ∧ N ≤ v ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' = C ∧
      (∀ p, p < v → E p v = delayedOldColumn F c' p s ∧
        E v p = delayedOldColumn F c' p s) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v)
          (delayedOldColumn F c')) = C ∧
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
          (protectedPivotColumn v
            (fun p u => delayedOldColumn F c' p (pi u)) beta)) =
        (fun U => C (integerGraphSupportImage pi U)) := by
  obtain ⟨F, c', hBF, hKeep, hRaw, hCanonical⟩ :=
    henson_leftDense_normalizes_finite_target_age
      E d ell b hell hAvoid hDense c C hAge hBelow
  obtain ⟨v, hFv, hNv, hColumn, hAt, hNext⟩ :=
    henson_leftDense_realizes_late_controlledCoding E d e ell F N hell
      hAvoid hDense c' s C hAge hCanonical X hCap hGrowth pi beta hPositive
  exact ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext⟩

/-- One common finite numerical stage after the SAME prepared and constructed
pivot. All target clique profiles share one embedding and numerical cutoff.
The nonempty survivor-sort premise is used only by the finite-stage API. -/
theorem henson_leftDense_prepares_controlled_age_stage
    (E : Nat → Nat → Bool) (d e ell b N k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (C : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell C)
    (hBelow : AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c))
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → C U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → C V = C U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    ∃ (F v : Nat) (c' : Nat → Fin d → Bool),
      b ≤ F ∧ F ≤ v ∧ N ≤ v ∧
      (∀ p, p < b → ∀ t, c' p t = c p t) ∧
      finiteOldColumnRawBound E ell d (Finset.range F) c' = C ∧
      (∀ p, p < v → E p v = delayedOldColumn F c' p s ∧
        E v p = delayedOldColumn F c' p s) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v)
          (delayedOldColumn F c')) = C ∧
      let Bcol := protectedPivotColumn v
        (fun p u => delayedOldColumn F c' p (pi u)) beta
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1)) Bcol) =
        (fun U => C (integerGraphSupportImage pi U)) ∧
      ∃ (f : Nat → Nat) (M : Nat),
        FiniteNumericStageWitness E e ell (v + 1) k he Bcol f M := by
  obtain ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext⟩ :=
    henson_leftDense_prepares_and_codes_controlled_age E d e ell b N hell
      hAvoid hDense c s C hAge hBelow X hCap hGrowth pi beta hPositive
  refine ⟨F, v, c', hBF, hFv, hNv, hKeep, hRaw, hColumn, hAt, hNext, ?_⟩
  exact henson_leftDense_finite_numeric_stage_witness E e ell (v + 1) k
    hell he hAvoid hDense
    (protectedPivotColumn v (fun p u => delayedOldColumn F c' p (pi u)) beta)

end Kk
