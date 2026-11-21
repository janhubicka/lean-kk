import Kk.ControlledPreAge
import Kk.LateControlledPivot
import Kk.K4SingletonOldNeighbour
import Mathlib.Tactic

/-!
# Derive a controlled pre-age from a prospective complete pivot event

The English argument and independent adversarial audit preceded this source
in `docs/track_b_controlled_preage_english_audit_20261121.md`, Section 5.

The prospective raw bound is calculated from the complete old columns and
the symbolic pivot type. It is proved equal to the literal raw bound of an
abstract one-point graph extension. Its canonical survivor age determines
the controlled pre-age. Positivity of the surviving sorts and the old pivot
singleton DERIVE the lower-bound inequality; it is not assumed.

No numerical pivot is selected in this algebraic calculation. A later
physical realization may normalize first and choose the pivot afterwards.
-/

namespace Kk

/-- Exact complete raw age after an abstract pivot of old sort j, with
positive survivor bits exactly on X. The pool on insert j U is a finite set
operation and does not evaluate an age on an oversized support. -/
noncomputable def prospectivePivotRaw
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (U : IntegerGraphSupport d ell) : Nat := by
  classical
  exact ell - 1 -
    (if U.1 ⊆ X then
      max (finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b) c U.1))
        (1 + finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c (insert j U.1)))
    else finiteDirectedCliqueCapacity E
      (oldSupportCommonNeighbourPool (Finset.range b) c U.1))

private theorem prospective_capacity_congr
    (E A : Nat → Nat → Bool) (P : Finset Nat)
    (hEdge : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → E p q = A p q) :
    finiteDirectedCliqueCapacity E P = finiteDirectedCliqueCapacity A P := by
  classical
  unfold finiteDirectedCliqueCapacity
  apply congrArg (fun W : Finset (Finset Nat) => W.sup Finset.card)
  ext Q
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hQP, hClique⟩
    refine ⟨hQP, ?_⟩
    intro p hp q hq hpq
    rw [← hEdge p (hQP hp) q (hQP hq) hpq]
    exact hClique p hp q hq hpq
  · rintro ⟨hQP, hClique⟩
    refine ⟨hQP, ?_⟩
    intro p hp q hq hpq
    rw [hEdge p (hQP hp) q (hQP hq) hpq]
    exact hClique p hp q hq hpq

/-- The prospective formula is the literal complete-prefix raw age of the
abstract one-point graph, not an independently chosen residual operation.
It holds without a freeness assumption, including raw zero values. -/
theorem prospectivePivotRaw_eq_abstract_extension
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d)) :
    prospectivePivotRaw E ell d b c j X =
      finiteOldColumnRawBound (onePointGraphEdge E b (fun p => c p j))
        ell d (Finset.range (b + 1))
        (protectedPivotColumn b c (fun t => decide (t ∈ X))) := by
  classical
  let A := onePointGraphEdge E b (fun p => c p j)
  have hErase : (Finset.range (b + 1)).erase b = Finset.range b := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hColumn : ∀ p ∈ Finset.range b, A p b = c p j ∧ A b p = c p j := by
    intro p hp
    exact ⟨onePointGraphEdge_right E b _ p (Finset.mem_range.mp hp),
      onePointGraphEdge_left E b _ p (Finset.mem_range.mp hp)⟩
  have hOldCapacity (S : Finset (Fin d)) :
      finiteDirectedCliqueCapacity A
          (oldSupportCommonNeighbourPool (Finset.range b) c S) =
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range b) c S) := by
    apply prospective_capacity_congr
    intro p hp q hq _
    exact onePointGraphEdge_old E b _ p q
      (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hq).1)
  funext U
  symm
  change finiteOldColumnRawBound A ell d (Finset.range (b + 1))
    (protectedPivotColumn b c (fun t => decide (t ∈ X))) U = _
  rw [protectedPivotRaw_eq_actual A ell b (b + 1) (by omega)]
  unfold protectedPivotRaw prospectivePivotRaw
  rw [hErase, oldSupportCommonNeighbourPool_mutual_pivot A
    (Finset.range b) c j b hColumn, hOldCapacity, hOldCapacity]
  simpa only [decide_eq_true_eq]

/-- Positive old pivot singleton age also proves that the abstract event
is a legal one-point graph extension of the fixed Henson prefix. -/
theorem prospectivePivotGraph_safe_of_positive_singleton
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (c : Nat → Fin d → Bool) (j : Fin d)
    (hPivot : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U) :
    ¬ HasCliqueBelow (onePointGraphEdge E b (fun p => c p j)) (b + 1) ell := by
  classical
  let S : IntegerGraphSupport d ell :=
    ⟨{j}, Finset.singleton_nonempty _, by simp only [Finset.card_singleton]; omega⟩
  have hCheck := finiteNeighbourCliqueCheck_false_of_positive_old_singleton
    E d ell b hell c j (hPivot S rfl)
  exact (onePointGraph_cliqueFree_iff_finite_certificate E b ell
    (fun p => c p j) (by omega)
    (hensonForbiddenFamily_no_prefix_cliques ell hell E hAvoid b)).mpr hCheck

/-- The prospective event never increases the old raw bounds. -/
theorem prospectivePivotRaw_le_old
    (E : Nat → Nat → Bool) (ell d b : Nat)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d)) :
    AgeLe (prospectivePivotRaw E ell d b c j X)
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  intro U
  unfold prospectivePivotRaw finiteOldColumnRawBound
  split_ifs <;> omega

/-- Every positive support has one unit less raw allowance, because the
abstract pivot itself belongs to its complete common-neighbour pool. -/
theorem prospectivePivotRaw_positive_cap
    (E : Nat → Nat → Bool) (ell d b : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (U : IntegerGraphSupport d ell) (hU : U.1 ⊆ X) :
    prospectivePivotRaw E ell d b c j X U ≤ ell - 2 := by
  classical
  rw [prospectivePivotRaw, if_pos hU]
  omega

/-- Derive the controlled pre-age below the actual old RAW bound. The
prospective survivor age supplies the pointed budgets through the explicit
capacity formula; no pointed inequality or desired C≤P is assumed.
Positive survivor values are essential for undoing truncated subtraction. -/
theorem controlledPreAge_le_old_raw_of_prospective
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (hX : X ⊆ Finset.univ.erase j)
    (R : IntegerGraphSupport d ell → Nat)
    (hR : IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R)
    (hBelow : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j → R U ≤ prospectivePivotRaw E ell d b c j X U)
    (hPivot : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ finiteOldColumnRawBound E ell d (Finset.range b) c U) :
    AgeLe (controlledPreAge R j X)
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  apply (controlledPreAge_le_iff R _ j X hX
    (fun U V hUV => finiteOldColumnRawBound_support_mono
      E ell d (Finset.range b) c U V hUV)).mpr
  refine ⟨?_, hPivot, ?_⟩
  · intro U hU
    exact (hBelow U hU).trans (prospectivePivotRaw_le_old E ell d b c j X U)
  · intro U V hUX hV
    have hUE : U.1 ⊆ Finset.univ.erase j := hUX.trans hX
    have hPositive := (hR.1 U hUE).1
    have hRaw := hBelow U hUE
    rw [prospectivePivotRaw, if_pos hUX] at hRaw
    unfold finiteOldColumnRawBound
    rw [hV]
    omega

/-- The prospective canonical survivor age determines a genuine controlled
pre-age below the complete old canonical age. Only positivity of its listed
survivor supports and the old pivot singleton are assumed; canonical
consistency, the positive-support cap, and C≤P are all derived. -/
theorem prospective_controlledPreAge_is_age_and_below
    (E : Nat → Nat → Bool) (d ell b : Nat) (hell : 2 ≤ ell)
    (c : Nat → Fin d → Bool) (j : Fin d) (X : Finset (Fin d))
    (hX : X ⊆ Finset.univ.erase j)
    (hSurvivors : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j →
      1 ≤ integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X) U)
    (hPivot : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U) :
    let R := integerGraphAgeCanonical d ell (prospectivePivotRaw E ell d b c j X)
    let C := controlledPreAge R j X
    IsIntegerGraphAge d ell C ∧
      AgeLe C (finiteOldColumnRawBound E ell d (Finset.range b) c) ∧
      AgeLe C (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)) ∧
      (∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → C U ≤ ell - 2) ∧
      (∀ U V : IntegerGraphSupport d ell,
        U.1 ⊆ X → V.1 = insert j U.1 → C V = C U + 1) := by
  classical
  let B := prospectivePivotRaw E ell d b c j X
  let R := integerGraphAgeCanonical d ell B
  let C := controlledPreAge R j X
  have hRAge : IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R :=
    integerGraphAgeCanonical_is_subfront_of_positive (by omega) B _ hSurvivors
  have hRBelow : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j → R U ≤ B U := by
    intro U _
    exact integerGraphAgeCanonical_le_raw d ell B U
  have hRCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → R U ≤ ell - 2 := by
    intro U hU
    exact (hRBelow U (hU.trans hX)).trans
      (prospectivePivotRaw_positive_cap E ell d b hell c j X U hU)
  have hAge : IsIntegerGraphAge d ell C := controlledPreAge_is_age hell R j X hRAge hX hRCap
  have hPivotRaw : ∀ U : IntegerGraphSupport d ell, U.1 = {j} →
      1 ≤ finiteOldColumnRawBound E ell d (Finset.range b) c U := by
    intro U hU
    exact (hPivot U hU).trans (integerGraphAgeCanonical_le_raw d ell _ U)
  have hRaw := controlledPreAge_le_old_raw_of_prospective
    E d ell b hell c j X hX R hRAge hRBelow hPivotRaw
  exact ⟨hAge, hRaw, integerGraphAgeCanonical_greatest d ell _ C hAge hRaw,
    controlledPreAge_positive_cap R j X hX hRCap,
    controlledPreAge_positive_growth R j X hX⟩

end Kk
