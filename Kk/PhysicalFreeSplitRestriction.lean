import Kk.PhysicalFreeSplitAge
import Kk.CanonicalAgeExtraBound
import Mathlib.Tactic

/-!
# Exact physical free-split restriction, including maximal parents

English proof and independent audit preceded the implementation:
`docs/track_b_exact_free_split_restriction_english_audit.md`.

There is no parent safety cap in these statements. The complete new canonical
age is the canonical restriction of the pulled-back old age at the positive
daughter. No nonempty daughter is asserted when its capacity is zero.
-/

namespace Kk

/-- A single positive daughter adds exactly one RAW singleton cap, while
retaining every old original's complete passing column. -/
theorem freeSplit_raw_eq_lowerAt {d e ell : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d) (u : Fin e)
    (hbv : b ≤ v) (hvH : v < H)
    (hFree : ∀ p, p < b → E p v = false ∧ E v p = false) :
    finiteOldColumnRawBound E ell e (Finset.range H)
        (pointedContinuationColumn b v c pi (fun t => decide (t = u))) =
      integerAgeLowerAt e ell
        (finiteOldColumnRawBound E ell e (Finset.range b)
          (fun p t => c p (pi t)))
        ⟨{u}, Finset.singleton_nonempty _, by simp; omega⟩ (ell - 2) := by
  classical
  let S : IntegerGraphSupport e ell :=
    ⟨{u}, Finset.singleton_nonempty _, by simp; omega⟩
  have hSingle (U : IntegerGraphSupport e ell) :
      (∀ t ∈ U.1, decide (t = u) = true) ↔ U = S := by
    constructor
    · intro hAll
      apply Subtype.ext
      change U.1 = {u}
      apply Finset.eq_singleton_iff_unique_mem.mpr
      obtain ⟨t, ht⟩ := U.2.1
      have htu : t = u := of_decide_eq_true (hAll t ht)
      refine ⟨htu ▸ ht, ?_⟩
      intro x hx
      exact of_decide_eq_true (hAll x hx)
    · rintro rfl t ht
      have htu : t = u := Finset.mem_singleton.mp ht
      simp [htu]
  funext U
  rw [freePointedContinuation_raw_eq E b v H hell c pi
    (fun t => decide (t = u)) hbv hvH hFree U]
  have hBase := finiteOldColumnRawBound_reindex E (Finset.range b) c pi U
  change (if ∀ t ∈ U.1, decide (t = u) = true then
      min (finiteOldColumnRawBound E ell d (Finset.range b) c
        (integerGraphSupportImage pi U)) (ell - 2)
    else finiteOldColumnRawBound E ell d (Finset.range b) c
      (integerGraphSupportImage pi U)) =
    integerAgeLowerAt e ell
      (finiteOldColumnRawBound E ell e (Finset.range b)
        (fun p t => c p (pi t))) S (ell - 2) U
  simp only [integerAgeLowerAt, hBase, hSingle U]

/-- Exact canonical free-split age for EVERY parent, including a maximal
one. The result retains all consequences of canonicalization of the new
singleton cap; no positivity or old-age consistency premise is needed. -/
theorem freeSplit_canonical_eq_restriction {d e ell : Nat}
    (E : Nat → Nat → Bool) (b v H : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d) (u : Fin e)
    (hbv : b ≤ v) (hvH : v < H)
    (hFree : ∀ p, p < b → E p v = false ∧ E v p = false) :
    integerGraphAgeCanonical e ell
        (finiteOldColumnRawBound E ell e (Finset.range H)
          (pointedContinuationColumn b v c pi (fun t => decide (t = u)))) =
      integerGraphAgeCanonical e ell
        (integerAgeLowerAt e ell
          (fun U => integerGraphAgeCanonical d ell
            (finiteOldColumnRawBound E ell d (Finset.range b) c)
            (integerGraphSupportImage pi U))
          ⟨{u}, Finset.singleton_nonempty _, by simp; omega⟩ (ell - 2)) := by
  rw [freeSplit_raw_eq_lowerAt E b v H hell c pi u hbv hvH hFree]
  rw [integerGraphAgeCanonical_lowerAt_canonical]
  have hOld : integerGraphAgeCanonical e ell
      (finiteOldColumnRawBound E ell e (Finset.range b)
        (fun p t => c p (pi t))) =
        fun U => integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c)
          (integerGraphSupportImage pi U) := by
    funext U
    exact finiteOldColumnCanonical_reindex E (Finset.range b) c pi (by omega) U
  rw [hOld]

/-- Construct the actual marker and finite numerical future for any split,
with its exact canonical restriction. A maximal parent needs no separately
postulated all-support budget. Empty/zero-capacity daughter profiles remain
honest possibilities of the general statement. -/
theorem henson_leftDense_constructs_exactFreeSplit_stage
    (E : Nat → Nat → Bool) (d e ell b k : Nat)
    (hell : 2 ≤ ell) (he : 0 < e)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool) (pi : Fin e → Fin d) (u : Fin e) :
    ∃ (v : Nat) (f : Nat → Nat) (M : Nat),
      b ≤ v ∧
      (∀ p, p < v → E p v = false ∧ E v p = false) ∧
      integerGraphAgeCanonical e ell
          (finiteOldColumnRawBound E ell e (Finset.range (v + 1))
            (pointedContinuationColumn b v c pi (fun t => decide (t = u)))) =
        integerGraphAgeCanonical e ell
          (integerAgeLowerAt e ell
            (fun U => integerGraphAgeCanonical d ell
              (finiteOldColumnRawBound E ell d (Finset.range b) c)
              (integerGraphSupportImage pi U))
            ⟨{u}, Finset.singleton_nonempty _, by simp; omega⟩ (ell - 2)) ∧
      FiniteNumericStageWitness E e ell (v + 1) k he
        (pointedContinuationColumn b v c pi (fun t => decide (t = u))) f M ∧
      (∀ p, p < v + 1 → f p = p) := by
  classical
  have hCheck : finiteNeighbourCliqueCheck E b (ell - 1)
      (fun _ => false) = false := by
    apply finiteNeighbourCliqueCheck_false_of_small_neighbour_set
    have hEmpty : oldNeighbourSet b (fun _ => false) = ∅ := by
      simp [oldNeighbourSet]
    rw [hEmpty, Finset.card_empty]
    omega
  obtain ⟨v, hbv, hZero⟩ := henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense b (fun _ => false) hCheck
  have hFreeAll : ∀ p, p < v → E p v = false ∧ E v p = false := by
    intro p hp
    simpa only [ite_self] using hZero p hp
  have hFree : ∀ p, p < b → E p v = false ∧ E v p = false := by
    intro p hp
    exact hFreeAll p (by omega)
  have hCanonical := freeSplit_canonical_eq_restriction
    E b v (v + 1) hell c pi u hbv (by omega) hFree
  obtain ⟨f, M, hStage⟩ := henson_leftDense_finite_numeric_stage_witness
    E e ell (v + 1) k hell he hAvoid hDense
    (pointedContinuationColumn b v c pi (fun t => decide (t = u)))
  exact ⟨v, f, M, hbv, hFreeAll, hCanonical, hStage, hStage.1⟩

end Kk
