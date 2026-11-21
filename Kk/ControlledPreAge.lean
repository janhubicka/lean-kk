import Kk.CoverSubfrontIntermediateLift
import Kk.ConcreteCanonicalMaximizers
import Kk.RawWitnessNormalization
import Kk.TrackFMonotoneRawLocality

/-!
# Constructing a controlled pre-age from its survivor age

The English proof and independent adversarial audit were committed first in
`docs/track_b_controlled_preage_english_audit_20261121.md`.

The survivor age is a genuine relative age on all sorts except the pivot.
The constructor adds one pivot coordinate, and its consistency witnesses are
constructed explicitly. No physical pivot, desired ambient age equality, or
chronological history is assumed.
-/

namespace Kk

/-- A canonical raw bound is a genuine relative age on every subfront where
its values are positive. Consistency is obtained from actual feasible
maximizers, then zeroing outside the subfront; it is not an extra premise. -/
theorem integerGraphAgeCanonical_is_subfront_of_positive
    {d ell : Nat} (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat) (E : Finset (Fin d))
    (hPos : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ E → 1 ≤ integerGraphAgeCanonical d ell B U) :
    IsSubfrontIntegerGraphAge d ell E (integerGraphAgeCanonical d ell B) := by
  classical
  constructor
  · intro U hU
    refine ⟨hPos U hU, ?_⟩
    exact finiteWitnessCanonical_le_cap
      (integerCliqueOnSupport (d := d) (ell := ell)) (ell - 1)
      (fun w T => integerCliqueOnSupport_le w T) B U
  · intro U hU
    obtain ⟨w, hBounds, hValue⟩ :=
      integerGraphAgeCanonical_has_feasible_maximizer d ell hell B U
    let wE := trackFZeroOutside d ell hell w E
    have hWE : WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell)) B wE := by
      intro V
      exact (trackFZeroOutside_le d ell hell w E V).trans (hBounds V)
    refine ⟨wE, ?_, ?_, ?_⟩
    · intro i hi
      simp [wE, trackFZeroOutside, hi]
    · intro V _
      exact witnessValue_le_canonical
        (integerCliqueOnSupport (d := d) (ell := ell)) B wE hWE V
    · exact (trackFZeroOutside_T_mass d ell hell w E U hU).trans hValue

/-- Extend an age by zero at the empty set. Arguments outside the support
cardinality bound also receive zero; all theorems using this extension supply
the relevant cardinality bound explicitly. -/
noncomputable def integerGraphAgeWithEmpty {d ell : Nat}
    (R : IntegerGraphSupport d ell → Nat) (S : Finset (Fin d)) : Nat := by
  classical
  exact if h : S.Nonempty ∧ S.card ≤ ell - 1 then R ⟨S, h⟩ else 0

@[simp] theorem integerGraphAgeWithEmpty_empty {d ell : Nat}
    (R : IntegerGraphSupport d ell → Nat) :
    integerGraphAgeWithEmpty R ∅ = 0 := by
  simp [integerGraphAgeWithEmpty]

@[simp] theorem integerGraphAgeWithEmpty_support {d ell : Nat}
    (R : IntegerGraphSupport d ell → Nat) (T : IntegerGraphSupport d ell) :
    integerGraphAgeWithEmpty R T.1 = R T := by
  simp [integerGraphAgeWithEmpty, T.2]

/-- Every bounded possibly empty survivor set has an attaining raw witness
supported on that set and satisfying every relative age bound. -/
theorem subfrontIntegerGraphAge_supported_raw_witness
    {d ell : Nat} (hell : 0 < ell) (E : Finset (Fin d))
    (R : IntegerGraphSupport d ell → Nat)
    (hR : IsSubfrontIntegerGraphAge d ell E R)
    (S : Finset (Fin d)) (hSE : S ⊆ E) (hCard : S.card ≤ ell - 1) :
    ∃ w : RawIntegerCliqueWeights d ell,
      (∀ i, i ∉ S → (w i).val = 0) ∧
      (∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ E → rawIntegerCliqueOnSupport w U ≤ R U) ∧
      S.sum (fun i => (w i).val) = integerGraphAgeWithEmpty R S := by
  classical
  let zero : Fin ell := ⟨0, hell⟩
  by_cases hS : S.Nonempty
  · let T : IntegerGraphSupport d ell := ⟨S, hS, hCard⟩
    obtain ⟨w, _, hBounds, hValue⟩ := hR.2 T hSE
    let wS : RawIntegerCliqueWeights d ell :=
      fun i => if i ∈ S then w.1 i else zero
    refine ⟨wS, ?_, ?_, ?_⟩
    · intro i hi
      simp [wS, hi, zero]
    · intro U hUE
      have hLe : rawIntegerCliqueOnSupport wS U ≤ integerCliqueOnSupport w U := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S <;> simp [wS, hi, zero]
      exact hLe.trans (hBounds U hUE)
    · have hSum : S.sum (fun i => (wS i).val) = integerCliqueOnSupport w T := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [wS, hi]
      rw [hSum, hValue]
      exact (integerGraphAgeWithEmpty_support R T).symm
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨fun _ => zero, ?_, ?_, ?_⟩
    · intro i _
      rfl
    · intro U _
      simp [rawIntegerCliqueOnSupport, zero]
    · simp [hEmpty, zero]

private theorem relative_raw_mass_le_empty
    {d ell : Nat} (E : Finset (Fin d))
    (R : IntegerGraphSupport d ell → Nat)
    (w : RawIntegerCliqueWeights d ell)
    (hW : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ E → rawIntegerCliqueOnSupport w U ≤ R U)
    (S : Finset (Fin d)) (hSE : S ⊆ E) (hCard : S.card ≤ ell - 1) :
    S.sum (fun i => (w i).val) ≤ integerGraphAgeWithEmpty R S := by
  classical
  by_cases hS : S.Nonempty
  · let T : IntegerGraphSupport d ell := ⟨S, hS, hCard⟩
    change rawIntegerCliqueOnSupport w T ≤ integerGraphAgeWithEmpty R T.1
    rw [integerGraphAgeWithEmpty_support]
    exact hW T hSE
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

private theorem raw_mass_inter_of_supported
    {d ell : Nat} (w : RawIntegerCliqueWeights d ell)
    (S U : Finset (Fin d))
    (hW : ∀ i, i ∉ S → (w i).val = 0) :
    U.sum (fun i => (w i).val) = (U ∩ S).sum (fun i => (w i).val) := by
  classical
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro i hiU hi
  exact hW i (by simpa [hiU] using hi)

private theorem raw_mass_erase_of_zero
    {d ell : Nat} (w : RawIntegerCliqueWeights d ell)
    (j : Fin d) (U : Finset (Fin d)) (hW : (w j).val = 0) :
    U.sum (fun i => (w i).val) = (U.erase j).sum (fun i => (w i).val) := by
  classical
  symm
  apply Finset.sum_subset (Finset.erase_subset j U)
  intro i hiU hi
  have hij : i = j := by simpa [hiU] using hi
  simpa [hij] using hW

/-- The explicit controlled pre-age. The pivot contributes one unit precisely
on the positive passing set, while all survivor constraints are retained. -/
noncomputable def controlledPreAge {d ell : Nat}
    (R : IntegerGraphSupport d ell → Nat) (j : Fin d)
    (X : Finset (Fin d)) (T : IntegerGraphSupport d ell) : Nat := by
  classical
  exact if j ∈ T.1 then
    max (integerGraphAgeWithEmpty R (T.1.erase j))
      (1 + integerGraphAgeWithEmpty R ((T.1.erase j) ∩ X))
    else R T

private theorem erase_subset_survivors {d : Nat} (j : Fin d)
    (S : Finset (Fin d)) : S.erase j ⊆ Finset.univ.erase j := by
  intro i hi
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, Finset.mem_univ _⟩

private theorem subset_survivors_of_not_mem {d : Nat} (j : Fin d)
    (S : Finset (Fin d)) (hj : j ∉ S) : S ⊆ Finset.univ.erase j := by
  intro i hi
  exact Finset.mem_erase.mpr ⟨by intro h; subst i; exact hj hi, Finset.mem_univ _⟩

private theorem controlled_zero_witness_respects
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d))
    (w : RawIntegerCliqueWeights d ell) (hj : (w j).val = 0)
    (hW : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j → rawIntegerCliqueOnSupport w U ≤ R U) :
    ∀ U, rawIntegerCliqueOnSupport w U ≤ controlledPreAge R j X U := by
  classical
  intro U
  by_cases hU : j ∈ U.1
  · rw [controlledPreAge, ite_eq_left hU]
    apply le_trans ?_ (le_max_left _ _)
    rw [rawIntegerCliqueOnSupport, raw_mass_erase_of_zero w j U.1 hj]
    exact relative_raw_mass_le_empty _ R w hW _ (erase_subset_survivors j U.1)
      ((Finset.card_le_card (Finset.erase_subset j U.1)).trans U.2.2)
  · rw [controlledPreAge, ite_eq_right hU]
    exact hW U (subset_survivors_of_not_mem j U.1 hU)

private noncomputable def controlledPivotOne {d ell : Nat} (hell : 2 ≤ ell)
    (w : RawIntegerCliqueWeights d ell) (j : Fin d) : RawIntegerCliqueWeights d ell :=
  fun i => if i = j then ⟨1, by omega⟩ else w i

private theorem controlledPivotOne_mass
    {d ell : Nat} (hell : 2 ≤ ell) (w : RawIntegerCliqueWeights d ell)
    (j : Fin d) (U : Finset (Fin d)) :
    U.sum (fun i => (controlledPivotOne hell w j i).val) =
      (if j ∈ U then 1 else 0) + (U.erase j).sum (fun i => (w i).val) := by
  classical
  by_cases hj : j ∈ U
  · rw [ite_eq_left hj, ← Finset.sum_erase_add U
      (fun i => (controlledPivotOne hell w j i).val) hj]
    have hErase : (U.erase j).sum (fun i => (controlledPivotOne hell w j i).val) =
        (U.erase j).sum (fun i => (w i).val) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [controlledPivotOne, (Finset.mem_erase.mp hi).1]
    rw [hErase]
    simp [controlledPivotOne, Nat.add_comm]
  · rw [ite_eq_right hj, Finset.erase_eq_of_notMem hj, Nat.zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by intro h; subst i; exact hj hi
    simp [controlledPivotOne, hij]

private theorem controlled_one_witness_respects
    {d ell : Nat} (hell : 2 ≤ ell) (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d))
    (w : RawIntegerCliqueWeights d ell)
    (hX : ∀ i, i ∉ X → (w i).val = 0)
    (hW : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j → rawIntegerCliqueOnSupport w U ≤ R U) :
    ∀ U, rawIntegerCliqueOnSupport (controlledPivotOne hell w j) U ≤
      controlledPreAge R j X U := by
  classical
  intro U
  rw [rawIntegerCliqueOnSupport, controlledPivotOne_mass]
  by_cases hU : j ∈ U.1
  · rw [ite_eq_left hU, controlledPreAge, ite_eq_left hU]
    apply le_trans ?_ (le_max_right _ _)
    apply Nat.add_le_add_left
    rw [raw_mass_inter_of_supported w X (U.1.erase j) hX]
    exact relative_raw_mass_le_empty _ R w hW _
      (Finset.inter_subset_left.trans (erase_subset_survivors j U.1))
      ((Finset.card_le_card (Finset.inter_subset_left.trans
        (Finset.erase_subset j U.1))).trans U.2.2)
  · rw [ite_eq_right hU, Nat.zero_add, Finset.erase_eq_of_notMem hU,
      controlledPreAge, ite_eq_right hU]
    exact hW U (subset_survivors_of_not_mem j U.1 hU)

/-- Construct a genuine age from a genuine survivor age and the all-support
cap on the positive passing set. The normalized consistency witnesses are
proved, rather than assumed as a desired pre-age property. -/
theorem controlledPreAge_is_age
    {d ell : Nat} (hell : 2 ≤ ell)
    (R : IntegerGraphSupport d ell → Nat) (j : Fin d) (X : Finset (Fin d))
    (hR : IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R)
    (hX : X ⊆ Finset.univ.erase j)
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → R U ≤ ell - 2) :
    IsIntegerGraphAge d ell (controlledPreAge R j X) := by
  classical
  apply (rawIntegerGraphAge_iff_normalized d ell (by omega) _).mp
  constructor
  · intro T
    by_cases hj : j ∈ T.1
    · rw [controlledPreAge, ite_eq_left hj]
      have hErase : integerGraphAgeWithEmpty R (T.1.erase j) ≤ ell - 1 := by
        unfold integerGraphAgeWithEmpty
        split_ifs with h
        · exact (hR.1 ⟨_, h⟩ (erase_subset_survivors j T.1)).2
        · omega
      have hInter : integerGraphAgeWithEmpty R ((T.1.erase j) ∩ X) ≤ ell - 2 := by
        unfold integerGraphAgeWithEmpty
        split_ifs with h
        · exact hCap ⟨_, h⟩ Finset.inter_subset_right
        · omega
      constructor
      · exact le_trans (by omega : 1 ≤ 1 + integerGraphAgeWithEmpty R ((T.1.erase j) ∩ X))
          (le_max_right _ _)
      · exact max_le hErase (by omega)
    · rw [controlledPreAge, ite_eq_right hj]
      exact hR.1 T (subset_survivors_of_not_mem j T.1 hj)
  · intro T
    by_cases hj : j ∈ T.1
    · let S := T.1.erase j
      let A := S ∩ X
      have hSCard : S.card ≤ ell - 1 :=
        (Finset.card_le_card (Finset.erase_subset j T.1)).trans T.2.2
      have hACard : A.card ≤ ell - 1 :=
        (Finset.card_le_card Finset.inter_subset_left).trans hSCard
      by_cases hMax : 1 + integerGraphAgeWithEmpty R A ≤ integerGraphAgeWithEmpty R S
      · obtain ⟨w, hOutside, hBounds, hValue⟩ :=
          subfrontIntegerGraphAge_supported_raw_witness (by omega) _ R hR S
            (erase_subset_survivors j T.1) hSCard
        have hZero : (w j).val = 0 := hOutside j (by simp [S])
        refine ⟨w, controlled_zero_witness_respects R j X w hZero hBounds, ?_⟩
        rw [rawIntegerCliqueOnSupport, raw_mass_erase_of_zero w j T.1 hZero]
        change S.sum (fun i => (w i).val) = _
        rw [hValue, controlledPreAge, ite_eq_left hj]
        exact (max_eq_left hMax).symm
      · obtain ⟨w, hOutside, hBounds, hValue⟩ :=
          subfrontIntegerGraphAge_supported_raw_witness (by omega) _ R hR A
            (Finset.inter_subset_right.trans hX) hACard
        have hOutsideX : ∀ i, i ∉ X → (w i).val = 0 := by
          intro i hi
          exact hOutside i (fun h => hi (Finset.mem_inter.mp h).2)
        refine ⟨controlledPivotOne hell w j,
          controlled_one_witness_respects hell R j X w hOutsideX hBounds, ?_⟩
        rw [rawIntegerCliqueOnSupport, controlledPivotOne_mass, ite_eq_left hj,
          raw_mass_inter_of_supported w X (T.1.erase j) hOutsideX]
        change 1 + A.sum (fun i => (w i).val) = _
        rw [hValue, controlledPreAge, ite_eq_left hj]
        exact (max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hMax))).symm
    · obtain ⟨w, hOutside, hBounds, hValue⟩ :=
        subfrontIntegerGraphAge_supported_raw_witness (by omega) _ R hR T.1
          (subset_survivors_of_not_mem j T.1 hj) T.2.2
      refine ⟨w, controlled_zero_witness_respects R j X w (hOutside j hj) hBounds, ?_⟩
      rw [controlledPreAge, ite_eq_right hj]
      exact hValue.trans (integerGraphAgeWithEmpty_support R T)

/-- The constructor agrees with the given age on every survivor support. -/
theorem controlledPreAge_survivor
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (U : IntegerGraphSupport d ell)
    (hU : U.1 ⊆ Finset.univ.erase j) : controlledPreAge R j X U = R U := by
  classical
  have hj : j ∉ U.1 := by
    intro h
    exact (Finset.mem_erase.mp (hU h)).1 rfl
  simp [controlledPreAge, hj]

/-- The distinguished pivot has singleton value one. -/
theorem controlledPreAge_singleton
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (U : IntegerGraphSupport d ell)
    (hU : U.1 = {j}) : controlledPreAge R j X U = 1 := by
  simp [controlledPreAge, hU]

/-- The all-support positive cap is inherited from the survivor age. -/
theorem controlledPreAge_positive_cap
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (hX : X ⊆ Finset.univ.erase j)
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → R U ≤ ell - 2) :
    ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X →
      controlledPreAge R j X U ≤ ell - 2 := by
  intro U hU
  rw [controlledPreAge_survivor R j X U (hU.trans hX)]
  exact hCap U hU

/-- Every admissible positive support gains exactly one when the pivot is
inserted. The explicit V argument matches the controlled-pivot budget API. -/
theorem controlledPreAge_positive_growth
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (hX : X ⊆ Finset.univ.erase j)
    (U V : IntegerGraphSupport d ell) (hU : U.1 ⊆ X)
    (hV : V.1 = insert j U.1) :
    controlledPreAge R j X V = controlledPreAge R j X U + 1 := by
  classical
  have hjU : j ∉ U.1 := by
    intro hj
    exact (Finset.mem_erase.mp (hX (hU hj))).1 rfl
  have hjV : j ∈ V.1 := by simp [hV]
  rw [controlledPreAge_survivor R j X U (hU.trans hX)]
  rw [controlledPreAge, ite_eq_left hjV, hV, Finset.erase_insert hjU,
    Finset.inter_eq_left.mpr hU, integerGraphAgeWithEmpty_support]
  omega

/-- Whenever the singleton and pair are admissible, the pair-based passing
criterion recovers exactly X. In particular all such pairs are available for
ell at least three. Positivity rules out a spurious passing equality. -/
theorem controlledPreAge_passing_iff
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d))
    (hR : IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R)
    (hX : X ⊆ Finset.univ.erase j)
    (x : Fin d) (hx : x ≠ j) (U V : IntegerGraphSupport d ell)
    (hU : U.1 = {x}) (hV : V.1 = insert j U.1) :
    controlledPreAge R j X V = controlledPreAge R j X U + 1 ↔ x ∈ X := by
  classical
  have hjU : j ∉ U.1 := by simpa [hU] using Ne.symm hx
  have hUE : U.1 ⊆ Finset.univ.erase j := subset_survivors_of_not_mem j U.1 hjU
  by_cases hxX : x ∈ X
  · have hUX : U.1 ⊆ X := by simpa [hU] using hxX
    exact ⟨fun _ => hxX, fun _ => controlledPreAge_positive_growth R j X hX U V hUX hV⟩
  · have hInter : U.1 ∩ X = ∅ := by simp [hU, hxX]
    have hjV : j ∈ V.1 := by simp [hV]
    have hValue : controlledPreAge R j X V = R U := by
      rw [controlledPreAge, ite_eq_left hjV, hV, Finset.erase_insert hjU,
        hInter, integerGraphAgeWithEmpty_empty, integerGraphAgeWithEmpty_support,
        Nat.add_zero]
      exact max_eq_left (hR.1 U hUE).1
    rw [hValue, controlledPreAge_survivor R j X U hUE]
    constructor
    · intro h
      omega
    · intro h
      exact False.elim (hxX h)

private theorem controlledPreAge_withEmpty_survivor
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X S : Finset (Fin d)) (hS : S ⊆ Finset.univ.erase j) :
    integerGraphAgeWithEmpty (controlledPreAge R j X) S =
      integerGraphAgeWithEmpty R S := by
  classical
  unfold integerGraphAgeWithEmpty
  split_ifs with h
  · exact controlledPreAge_survivor R j X ⟨S, h⟩ hS
  · rfl

private theorem integerGraphAgeWithEmpty_le_of_subset
    {d ell : Nat} (R : IntegerGraphSupport d ell → Nat)
    (hR : IsIntegerGraphAge d ell R) (S : Finset (Fin d))
    (T : IntegerGraphSupport d ell) (hST : S ⊆ T.1) :
    integerGraphAgeWithEmpty R S ≤ R T := by
  classical
  unfold integerGraphAgeWithEmpty
  split_ifs with h
  · exact integerGraphAge_monotone d ell R hR ⟨S, h⟩ T hST
  · exact Nat.zero_le _

/-- The final manuscript controlled axiom: each support value is the maximum
of its survivor part and its positive part together with the pivot. Empty
parts are interpreted by the explicit zero extension. -/
theorem controlledPreAge_max_decomposition
    {d ell : Nat} (hell : 2 ≤ ell)
    (R : IntegerGraphSupport d ell → Nat) (j : Fin d) (X : Finset (Fin d))
    (hR : IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R)
    (hX : X ⊆ Finset.univ.erase j)
    (hCap : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ X → R U ≤ ell - 2)
    (T : IntegerGraphSupport d ell) :
    controlledPreAge R j X T =
      max (integerGraphAgeWithEmpty (controlledPreAge R j X) (T.1.erase j))
        (integerGraphAgeWithEmpty (controlledPreAge R j X) (T.1 ∩ insert j X)) := by
  classical
  by_cases hj : j ∈ T.1
  · rw [controlledPreAge_withEmpty_survivor R j X _ (erase_subset_survivors j T.1)]
    let Z := T.1 ∩ insert j X
    have hjZ : j ∈ Z := Finset.mem_inter.mpr ⟨hj, Finset.mem_insert_self _ _⟩
    let V : IntegerGraphSupport d ell :=
      ⟨Z, ⟨j, hjZ⟩, (Finset.card_le_card Finset.inter_subset_left).trans T.2.2⟩
    have hErase : Z.erase j = (T.1.erase j) ∩ X := by
      ext i
      simp only [Z, Finset.mem_erase, Finset.mem_inter, Finset.mem_insert]
      tauto
    have hZX : (Z.erase j) ∩ X = Z.erase j := by
      rw [hErase, Finset.inter_assoc, Finset.inter_self]
    have hSecond : integerGraphAgeWithEmpty (controlledPreAge R j X) Z =
        1 + integerGraphAgeWithEmpty R ((T.1.erase j) ∩ X) := by
      change integerGraphAgeWithEmpty (controlledPreAge R j X) V.1 = _
      rw [integerGraphAgeWithEmpty_support, controlledPreAge, ite_eq_left hjZ]
      change max (integerGraphAgeWithEmpty R (Z.erase j))
        (1 + integerGraphAgeWithEmpty R ((Z.erase j) ∩ X)) = _
      rw [hZX, hErase]
      omega
    rw [hSecond]
    exact ite_eq_left hj
  · rw [Finset.erase_eq_of_notMem hj, integerGraphAgeWithEmpty_support]
    symm
    apply max_eq_left
    exact integerGraphAgeWithEmpty_le_of_subset _
      (controlledPreAge_is_age hell R j X hR hX hCap) _ T Finset.inter_subset_left

/-- The survivor restriction, pivot singleton, positive growth and final
maximum axiom uniquely determine the controlled pre-age. This is a structural
uniqueness theorem; no additional consistency hypothesis is needed here. -/
theorem controlledPreAge_unique
    {d ell : Nat} (R F : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d))
    (hSurvivor : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ Finset.univ.erase j → F U = R U)
    (hSingleton : ∀ U : IntegerGraphSupport d ell, U.1 = {j} → F U = 1)
    (hGrowth : ∀ U V : IntegerGraphSupport d ell,
      U.1 ⊆ X → V.1 = insert j U.1 → F V = F U + 1)
    (hMax : ∀ T : IntegerGraphSupport d ell,
      F T = max (integerGraphAgeWithEmpty F (T.1.erase j))
        (integerGraphAgeWithEmpty F (T.1 ∩ insert j X))) :
    F = controlledPreAge R j X := by
  classical
  have hSurvivorEmpty : ∀ S : Finset (Fin d), S ⊆ Finset.univ.erase j →
      integerGraphAgeWithEmpty F S = integerGraphAgeWithEmpty R S := by
    intro S hS
    unfold integerGraphAgeWithEmpty
    split_ifs with h
    · exact hSurvivor ⟨S, h⟩ hS
    · rfl
  funext T
  by_cases hj : j ∈ T.1
  · let A := (T.1.erase j) ∩ X
    let Z := T.1 ∩ insert j X
    have hjZ : j ∈ Z := Finset.mem_inter.mpr ⟨hj, Finset.mem_insert_self _ _⟩
    have hZinsert : Z = insert j A := by
      ext i
      simp only [Z, A, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hiT, hi⟩
        rcases hi with rfl | hiX
        · exact Or.inl rfl
        · by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr ⟨⟨hij, hiT⟩, hiX⟩
      · rintro (rfl | ⟨⟨_, hiT⟩, hiX⟩)
        · exact ⟨hj, Or.inl rfl⟩
        · exact ⟨hiT, Or.inr hiX⟩
    let V : IntegerGraphSupport d ell :=
      ⟨Z, ⟨j, hjZ⟩, (Finset.card_le_card Finset.inter_subset_left).trans T.2.2⟩
    have hSecond : integerGraphAgeWithEmpty F Z = 1 + integerGraphAgeWithEmpty R A := by
      change integerGraphAgeWithEmpty F V.1 = _
      rw [integerGraphAgeWithEmpty_support]
      by_cases hA : A.Nonempty
      · let U : IntegerGraphSupport d ell :=
          ⟨A, hA, (Finset.card_le_card (Finset.inter_subset_left.trans
            (Finset.erase_subset j T.1))).trans T.2.2⟩
        rw [hGrowth U V Finset.inter_subset_right hZinsert,
          hSurvivor U (Finset.inter_subset_left.trans (erase_subset_survivors j T.1))]
        change R U + 1 = 1 + integerGraphAgeWithEmpty R U.1
        rw [integerGraphAgeWithEmpty_support, Nat.add_comm]
      · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
        have hV : V.1 = {j} := by simpa only [hEmpty, insert_empty_eq] using hZinsert
        rw [hSingleton V hV, hEmpty, integerGraphAgeWithEmpty_empty, Nat.add_zero]
    rw [hMax T, hSurvivorEmpty _ (erase_subset_survivors j T.1), hSecond]
    exact (ite_eq_left hj).symm
  · rw [hSurvivor T (subset_survivors_of_not_mem j T.1 hj), controlledPreAge,
      ite_eq_right hj]

/-- Exact minimality criterion for the explicit constructor. It only requires
support monotonicity of P. The singleton test handles empty positive support;
the pointed tests use nonempty U and an explicitly admissible insertion V. -/
theorem controlledPreAge_le_iff
    {d ell : Nat} (R P : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (hX : X ⊆ Finset.univ.erase j)
    (hP : ∀ U V : IntegerGraphSupport d ell, U.1 ⊆ V.1 → P U ≤ P V) :
    AgeLe (controlledPreAge R j X) P ↔
      (∀ U : IntegerGraphSupport d ell, U.1 ⊆ Finset.univ.erase j → R U ≤ P U) ∧
      (∀ U : IntegerGraphSupport d ell, U.1 = {j} → 1 ≤ P U) ∧
      (∀ U V : IntegerGraphSupport d ell, U.1 ⊆ X → V.1 = insert j U.1 →
        R U + 1 ≤ P V) := by
  classical
  constructor
  · intro hBelow
    refine ⟨?_, ?_, ?_⟩
    · intro U hU
      simpa only [controlledPreAge_survivor R j X U hU] using hBelow U
    · intro U hU
      simpa only [controlledPreAge_singleton R j X U hU] using hBelow U
    · intro U V hU hV
      have h := hBelow V
      rw [controlledPreAge_positive_growth R j X hX U V hU hV,
        controlledPreAge_survivor R j X U (hU.trans hX)] at h
      exact h
  · rintro ⟨hSurvivor, hSingleton, hPointed⟩ T
    by_cases hj : j ∈ T.1
    · rw [controlledPreAge, ite_eq_left hj]
      apply max_le
      · unfold integerGraphAgeWithEmpty
        split_ifs with hS
        · exact (hSurvivor ⟨_, hS⟩ (erase_subset_survivors j T.1)).trans
            (hP _ T (Finset.erase_subset j T.1))
        · exact Nat.zero_le _
      · let A := (T.1.erase j) ∩ X
        have hAT : A ⊆ T.1 :=
          Finset.inter_subset_left.trans (Finset.erase_subset j T.1)
        have hInsert : insert j A ⊆ T.1 := Finset.insert_subset_iff.mpr ⟨hj, hAT⟩
        by_cases hA : A.Nonempty
        · let U : IntegerGraphSupport d ell :=
            ⟨A, hA, (Finset.card_le_card hAT).trans T.2.2⟩
          let V : IntegerGraphSupport d ell :=
            ⟨insert j A, Finset.insert_nonempty _ _,
              (Finset.card_le_card hInsert).trans T.2.2⟩
          change 1 + integerGraphAgeWithEmpty R U.1 ≤ P T
          rw [integerGraphAgeWithEmpty_support, Nat.add_comm]
          exact (hPointed U V Finset.inter_subset_right rfl).trans (hP V T hInsert)
        · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
          let V : IntegerGraphSupport d ell :=
            ⟨{j}, Finset.singleton_nonempty _,
              (Finset.card_le_card (Finset.singleton_subset_iff.mpr hj)).trans T.2.2⟩
          change 1 + integerGraphAgeWithEmpty R A ≤ P T
          rw [hEmpty, integerGraphAgeWithEmpty_empty, Nat.add_zero]
          exact (hSingleton V rfl).trans (hP V T (Finset.singleton_subset_iff.mpr hj))
    · rw [controlledPreAge, ite_eq_right hj]
      exact hSurvivor T (subset_survivors_of_not_mem j T.1 hj)

/-- For a genuine ambient age the singleton test is automatic, leaving
precisely survivor domination and the nonempty pointed inequalities. -/
theorem controlledPreAge_le_iff_of_age
    {d ell : Nat} (R P : IntegerGraphSupport d ell → Nat)
    (j : Fin d) (X : Finset (Fin d)) (hX : X ⊆ Finset.univ.erase j)
    (hP : IsIntegerGraphAge d ell P) :
    AgeLe (controlledPreAge R j X) P ↔
      (∀ U : IntegerGraphSupport d ell, U.1 ⊆ Finset.univ.erase j → R U ≤ P U) ∧
      (∀ U V : IntegerGraphSupport d ell, U.1 ⊆ X → V.1 = insert j U.1 →
        R U + 1 ≤ P V) := by
  rw [controlledPreAge_le_iff R P j X hX
    (fun U V hUV => integerGraphAge_monotone d ell P hP U V hUV)]
  constructor
  · rintro ⟨hSurvivor, _, hPointed⟩
    exact ⟨hSurvivor, hPointed⟩
  · rintro ⟨hSurvivor, hPointed⟩
    exact ⟨hSurvivor, fun U _ => (hP.1 U).1, hPointed⟩

end Kk
