import Kk.PhysicalControlledCoding
import Mathlib.Tactic

/-!
# A late actual coding pivot from the complete prepared prefix

The English proof and independent adversarial audit were committed first in
`docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`.

Positive canonical singleton age supplies the complete old-neighbourhood
certificate. The actual pivot is chosen after the whole finite preparation,
beyond any requested cutoff. All intervening columns are zero, so the age
at the chronological pivot cut is derived from the prepared age. The same
chosen vertex is then used by the verified controlled-coding theorem.

Every previously committed original must lie below the protected cutoff.
This does not preserve already fixed positive future columns beyond that
cutoff, or assert dependent Kpt history or an infinite resolved diary.
-/

namespace Kk

/-- Positive canonical singleton age excludes every forbidden clique in
the COMPLETE prescribed neighbourhood. No separate legality condition or
bound on the number of old neighbours is assumed. -/
theorem finiteNeighbourCliqueCheck_false_of_positive_old_singleton
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (hPos : 1 ≤ integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c)
      ⟨{s}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩) :
    finiteNeighbourCliqueCheck E b (ell - 1) (fun p => c p s) = false := by
  classical
  let S : IntegerGraphSupport d ell :=
    ⟨{s}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩
  have hRaw := integerGraphAgeCanonical_le_raw d ell
    (finiteOldColumnRawBound E ell d (Finset.range b) c) S
  have hPos' : 1 ≤ integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) S := hPos
  have hCapacity : finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range b) c S.1) < ell - 1 := by
    change integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) S ≤
      ell - 1 - finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c S.1) at hRaw
    omega
  apply (finiteNeighbourCliqueCheck_false_iff E b (ell - 1)
    (fun p => c p s)).mpr
  rintro ⟨Q, hCard, hBound, hClique⟩
  have hSub : Q ⊆ oldSupportCommonNeighbourPool (Finset.range b) c S.1 := by
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hBound p hp).1, ?_⟩
    intro t ht
    have hts : t = s := Finset.mem_singleton.mp ht
    simpa only [hts] using (hBound p hp).2
  have hCardLe := directedClique_card_le_capacity E
    (oldSupportCommonNeighbourPool (Finset.range b) c S.1) Q hSub hClique
  omega

/-- A positive symbolic singleton has a genuine later original realization
after ANY requested cutoff. Both directions of every old edge and every
gap zero are exact. The whole raw and canonical pre-ages are derived at the
actual chronological cut, not separately postulated there. -/
theorem henson_leftDense_realizes_late_positive_sort
    (E : Nat → Nat → Bool) (d ell b N : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (hPos : 1 ≤ integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c)
      ⟨{s}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩) :
    ∃ v : Nat, b ≤ v ∧ N ≤ v ∧
      (∀ p, p < v → E p v = delayedOldColumn b c p s ∧
        E v p = delayedOldColumn b c p s) ∧
      finiteOldColumnRawBound E ell d (Finset.range v) (delayedOldColumn b c) =
        finiteOldColumnRawBound E ell d (Finset.range b) c ∧
      integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range v) (delayedOldColumn b c)) =
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  let D := max b N
  let C := delayedOldColumn b c
  have hbD : b ≤ D := le_max_left _ _
  have hND : N ≤ D := le_max_right _ _
  have hDelay : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range D) C) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) :=
    delayedOldCanonicalAge_eq E ell d b D hbD c
  have hPosD : 1 ≤ integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range D) C)
      ⟨{s}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩ := by
    rw [hDelay]
    exact hPos
  have hCheck := finiteNeighbourCliqueCheck_false_of_positive_old_singleton
    E d ell D hell C s hPosD
  obtain ⟨v, hDv, hColumn⟩ := henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense D (fun p => C p s) hCheck
  have hbv : b ≤ v := hbD.trans hDv
  refine ⟨v, hbv, hND.trans hDv, ?_,
    delayedOldRawBound_eq E ell d b v hbv c,
    delayedOldCanonicalAge_eq E ell d b v hbv c⟩
  intro p hp
  have h := hColumn p hp
  by_cases hpD : p < D
  · simpa only [if_pos hpD] using h
  · have hbp : b ≤ p := by omega
    have hZero : delayedOldColumn b c p s = false :=
      delayedOldColumn_padding_zero b c p s hbp
    simpa only [if_neg hpD, hZero] using h

/-- After finite preparation, a controlled age can be coded at one
constructed later pivot. All complete prepared columns survive, and the
full next-prefix canonical age is the prescribed parent pullback. -/
theorem henson_leftDense_realizes_late_controlledCoding
    (E : Nat → Nat → Bool) (d e ell b N : Nat)
    (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → F U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → F V = F U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    ∃ v : Nat, b ≤ v ∧ N ≤ v ∧
      (∀ p, p < v → E p v = delayedOldColumn b c p s ∧
        E v p = delayedOldColumn b c p s) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v) (delayedOldColumn b c)) = F ∧
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
          (protectedPivotColumn v
            (fun p u => delayedOldColumn b c p (pi u)) beta)) =
        (fun U => F (integerGraphSupportImage pi U)) := by
  classical
  let S : IntegerGraphSupport d ell :=
    ⟨{s}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩
  have hPos : 1 ≤ integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) S := by
    rw [hOld]
    exact (hAge.1 S).1
  obtain ⟨v, hbv, hNv, hColumn, _hRaw, hCanonical⟩ :=
    henson_leftDense_realizes_late_positive_sort
      E d ell b N hell hAvoid hDense c s hPos
  have hAt : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range v) (delayedOldColumn b c)) = F :=
    hCanonical.trans hOld
  exact ⟨v, hbv, hNv, hColumn, hAt,
    controlledCoding_next_prefix_canonical_eq E d e ell v hell
      (delayedOldColumn b c) s hColumn F hAge hAt X hCap hGrowth pi beta hPositive⟩

/-- The same late coding pivot and one common finite numerical Henson
stage realize every permitted joint future profile. The stage fixes the
entire actual prefix through the chosen pivot. -/
theorem henson_leftDense_constructs_late_controlledCoding_stage
    (E : Nat → Nat → Bool) (d e ell b N k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (s : Fin d)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hOld : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = F)
    (X : Finset (Fin d))
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → F U ≤ ell - 2)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert s U.1 → F V = F U + 1)
    (pi : Fin e → Fin d) (beta : Fin e → Bool)
    (hPositive : ∀ u, beta u = true → pi u ∈ X) :
    ∃ v : Nat, b ≤ v ∧ N ≤ v ∧
      (∀ p, p < v → E p v = delayedOldColumn b c p s ∧
        E v p = delayedOldColumn b c p s) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range v) (delayedOldColumn b c)) = F ∧
      let C := protectedPivotColumn v
        (fun p u => delayedOldColumn b c p (pi u)) beta
      integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range (v + 1)) C) =
        (fun U => F (integerGraphSupportImage pi U)) ∧
      ∃ (f : Nat → Nat) (M : Nat),
        FiniteNumericStageWitness E e ell (v + 1) k he C f M := by
  obtain ⟨v, hbv, hNv, hColumn, hAt, hNext⟩ :=
    henson_leftDense_realizes_late_controlledCoding E d e ell b N hell
      hAvoid hDense c s F hAge hOld X hCap hGrowth pi beta hPositive
  refine ⟨v, hbv, hNv, hColumn, hAt, hNext, ?_⟩
  exact henson_leftDense_finite_numeric_stage_witness E e ell (v + 1) k
    hell he hAvoid hDense
    (protectedPivotColumn v (fun p u => delayedOldColumn b c p (pi u)) beta)

end Kk
