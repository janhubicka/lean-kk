import Kk.PartialNumericCommonPool
import Kk.FullBlockActualAge
import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Track A: monotone actual numerical-H old-prefix capacities

Mathematical proof and adversarial checks were committed BEFORE
Lean in docs/partial_numeric_age_monotonicity_english_audit.md.

As a partial original-block cut advances, the TRUE numbered old
U-neighbourhood against a FIXED family of future top-original names
only enlarges. Its directed clique capacity is monotone, and its
raw future integer age (ell-1 minus capacity) is antitone.

At g=0 the actual full numbered old-prefix raw age is exactly
the original old age, by FullBlockActualAge, so all partial-cut
raw bounds lie below that original old age pointwise.

This does not identify strict cover transitions, the actual
recursive stage schedule or full parameter-closed E/B3 data.
-/

namespace Kk

open SuccessorTree.V10

/-- Every actual old U-common-neighbourhood is monotone
along literal numbered prefixes of one original block,
with all odd dummies included. No symmetry is needed here:
it is pure containment in the SAME actual binary-L table. -/
theorem finiteNumericH_partial_actual_common_pool_mono
    {d ell : Nat} (E : Nat → Nat → Bool)
    (k b M g h : Nat) (hgh : g ≤ h)
    (j : Fin d → Nat) (U : IntegerGraphSupport d ell) :
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b g))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U.1 ⊆
    oldSupportCommonNeighbourPool
      (Finset.range (hPosition k b h))
      (fun z t => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1)) U.1 := by
  classical
  intro z hz
  obtain ⟨hzRange,hAll⟩ := Finset.mem_filter.mp hz
  have hCut : hPosition k b g ≤ hPosition k b h := by
    change 2 * (k + 1) * b + 2 * g ≤
      2 * (k + 1) * b + 2 * h
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hgh)
      (2 * (k + 1) * b)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hzRange) hCut),hAll⟩

/-- True directed clique capacity can only grow as the
actual numbered prefix advances, for each nonempty support.
The same physical binary L table is used on both sides. -/
theorem finiteNumericH_partial_actual_capacity_mono
    {d ell : Nat} (E : Nat → Nat → Bool)
    (k b M g h : Nat) (hgh : g ≤ h)
    (j : Fin d → Nat) (U : IntegerGraphSupport d ell) :
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) ≤
    finiteDirectedCliqueCapacity
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
      (oldSupportCommonNeighbourPool
        (Finset.range (hPosition k b h))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U.1) := by
  exact finiteDirectedCliqueCapacity_mono
    (fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
    _ _
    (finiteNumericH_partial_actual_common_pool_mono
      E k b M g h hgh j U)

/-- The actual old raw age is ANTITONE under a growing old
numerical-H prefix. This is a pointwise function inequality:
no unwarranted positivity or genuine graph-age claim. -/
theorem finiteNumericH_partial_actual_raw_age_antitone
    {d : Nat} (E : Nat → Nat → Bool)
    (ell k b M g h : Nat) (hgh : g ≤ h)
    (j : Fin d → Nat) :
    ∀ U : IntegerGraphSupport d ell,
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b h))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U ≤
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U := by
  intro U
  have hCap := finiteNumericH_partial_actual_capacity_mono
    E k b M g h hgh j U
  unfold finiteOldColumnRawBound
  omega

/-- Every partial cut g<=k has actual raw age at most the
ORIGINAL old age of the full earlier original block prefix,
provided E is symmetric and every given selected top lies
strictly beyond the current original.  At g=0 there is equality. -/
theorem finiteNumericH_partial_actual_raw_age_le_original
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g M : Nat) (hg : g ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    ∀ U : IntegerGraphSupport d ell,
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b g))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U ≤
      finiteOldColumnRawBound E ell d (Finset.range b)
        (fun i t => E i (j t)) U := by
  intro U
  have hMono := finiteNumericH_partial_actual_raw_age_antitone
    E ell k b M 0 g (Nat.zero_le g) j U
  have hFull :
      finiteOldColumnRawBound
        (fun x y => (finiteNumericHL
          (normalizedGraphModel E) k M).binary x y (0 : Fin 1))
        ell d (Finset.range (hPosition k b 0))
        (fun z t => (finiteNumericHL
          (normalizedGraphModel E) k M).binary
            z (hPosition k (j t) k) (0 : Fin 1)) U =
      finiteOldColumnRawBound E ell d (Finset.range b)
        (fun i t => E i (j t)) U :=
    congrFun
      (finiteNumericH_full_block_actual_raw_age_eq_original
        E hSym ell k b M j (fun t => le_of_lt (hj t))) U
  exact hMono.trans (le_of_eq hFull)

#print axioms Kk.finiteNumericH_partial_actual_common_pool_mono
#print axioms Kk.finiteNumericH_partial_actual_capacity_mono
#print axioms Kk.finiteNumericH_partial_actual_raw_age_antitone
#print axioms Kk.finiteNumericH_partial_actual_raw_age_le_original

end Kk
