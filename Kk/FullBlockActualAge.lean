import Kk.FullBlockActualTopColumn
import Kk.FullNumericBlockPrefixAge
import Mathlib.Tactic

/-!
# Track A: the TRUE selected-top old-column age at a COMPLETE numeric block cut

English proof and adversarial review were committed first:
  docs/full_block_actual_age_english_audit.md

In the real finite numerical-H binary L, the complete old prefix's
raw graph age against a given finite collection of later top-originals
is exactly the original old-prefix raw age against their actual
original E columns. The associated canonical age and feasible
integer weight profiles coincide as well. This is a finite,
completed-block theorem; it does not construct later original names
or verify a recursive reserved-pivot/mixed-neighbourhood schedule.
-/

namespace Kk

open SuccessorTree.V10

/-- The TRUE old-to-later-top numerical-H L crossing columns
calculate exactly the original old-prefix raw age at every
nonempty admissible support, without discarding odd dummies
or intermediate real generations from the old numeric prefix. -/
theorem finiteNumericH_full_block_actual_raw_age_eq_original
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b M : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b ≤ j t) :
    finiteOldColumnRawBound
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      ell d (Finset.range (hPosition k b 0))
      (fun z t =>
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) =
    finiteOldColumnRawBound E ell d (Finset.range b)
      (fun i t => E i (j t)) := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1)
  let P : Finset Nat := Finset.range (hPosition k b 0)
  let c : Nat → Fin d → Bool := fun i t => E i (j t)
  let actual : Nat → Fin d → Bool :=
    fun z t => L z (hPosition k (j t) k)
  have hSameCommon :
      ∀ U : IntegerGraphSupport d ell,
        oldSupportCommonNeighbourPool P actual U.1 =
        oldSupportCommonNeighbourPool P
          (numericHFullBlockOldColumn k b c) U.1 := by
    intro U
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzPool,hAll⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨hzPool,?_⟩
      intro t ht
      have hEq :=
        (finiteNumericH_full_block_actual_top_column_both
          E hSym k b M j hj z (Finset.mem_range.mp hzPool) t).1
      change actual z t =
        numericHFullBlockOldColumn k b c z t at hEq
      exact hEq.symm.trans (hAll t ht)
    · intro hz
      obtain ⟨hzPool,hAll⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨hzPool,?_⟩
      intro t ht
      have hEq :=
        (finiteNumericH_full_block_actual_top_column_both
          E hSym k b M j hj z (Finset.mem_range.mp hzPool) t).1
      change actual z t =
        numericHFullBlockOldColumn k b c z t at hEq
      exact hEq.trans (hAll t ht)
  have hSameRaw :
      finiteOldColumnRawBound L ell d P actual =
      finiteOldColumnRawBound L ell d P
        (numericHFullBlockOldColumn k b c) := by
    funext U
    unfold finiteOldColumnRawBound
    rw [hSameCommon U]
  change finiteOldColumnRawBound L ell d P actual =
    finiteOldColumnRawBound E ell d (Finset.range b) c
  exact hSameRaw.trans
    (finiteNumericH_full_block_raw_age_eq_original
      E hSym ell d k b M c)

/-- Canonical integer old age of ACTUAL later-top columns is
unchanged by the full numerical-H original-block expansion. -/
theorem finiteNumericH_full_block_actual_canonical_age_eq_original
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b M : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b ≤ j t) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b 0))
        (fun z t =>
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1))) =
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b)
        (fun i t => E i (j t))) := by
  rw [finiteNumericH_full_block_actual_raw_age_eq_original
    E hSym ell k b M j hj]

/-- Every feasible normalized labelled clique multiplicity
family is unchanged for the ACTUAL future top-original columns
at a fully completed old numeric original-block cut. -/
theorem finiteNumericH_full_block_actual_feasible_eq_original
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b M : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b ≤ j t) :
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b 0))
        (fun z t =>
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1))) =
    feasibleIntegerCliqueVectors d ell
      (finiteOldColumnRawBound E ell d (Finset.range b)
        (fun i t => E i (j t))) := by
  rw [finiteNumericH_full_block_actual_raw_age_eq_original
    E hSym ell k b M j hj]

#print axioms Kk.finiteNumericH_full_block_actual_raw_age_eq_original
#print axioms Kk.finiteNumericH_full_block_actual_canonical_age_eq_original
#print axioms Kk.finiteNumericH_full_block_actual_feasible_eq_original

end Kk
