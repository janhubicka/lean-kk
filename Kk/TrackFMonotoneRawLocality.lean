import Kk.TrackFLiteralWordColumns
import Kk.IntegerAgeLocality
import Mathlib.Tactic

/-!
# Track F: canonicalization is local on supports for monotone raw bounds

A raw common-symbol capacity of actual concrete words is support-monotone
(proved in TrackFLiteralWordColumns). This structural property is
essential for deleting a coded branch: an arbitrary raw bound need not
commute with restriction.

Here we prove the *same-index* finite canonicalization locality theorem.
If monotone raw B,C agree on every nonempty support inside T, then their
actual normalized clique-witness maxima G_B(T),G_C(T) coincide. The proof
uses explicit zeroing of a normalized witness outside T, checks EVERY
global support constraint, and handles empty intersections separately.

This is not yet the finite reindexing into Fin (d-1) after deletion,
nor full abstract/concrete diary equivalence, E passing bits, splitting,
or independent infinite big Ramsey unavoidability.
-/

namespace Kk

/-- Support-monotonicity of an arbitrary raw bound, which need not
be an admissible graph age or its own canonicalization. -/
def TrackFRawSupportMonotone
    (d ell : Nat) (B : IntegerGraphSupport d ell → Nat) : Prop :=
  ∀ U V : IntegerGraphSupport d ell,
    U.1 ⊆ V.1 → B U ≤ B V

/-- Set all normalized clique multiplicities outside T to zero.
The total size remains bounded by ell-1. -/
noncomputable def trackFZeroOutside
    (d ell : Nat) (hell : 0 < ell)
    (w : IntegerCliqueWeights d ell)
    (T : Finset (Fin d)) : IntegerCliqueWeights d ell := by
  classical
  let zero : Fin ell := ⟨0, hell⟩
  let wT : Fin d → Fin ell :=
    fun j => if j ∈ T then w.1 j else zero
  have hTotal :
      Finset.univ.sum (fun j : Fin d => (wT j).val) ≤ ell - 1 := by
    calc
      _ ≤ Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j ∈ T
        · simp [wT,h]
        · simp [wT,h,zero]
      _ ≤ ell - 1 := w.2
  exact ⟨wT,hTotal⟩

/-- Zeroing outside T cannot increase any admissible clique support mass. -/
theorem trackFZeroOutside_le
    (d ell : Nat) (hell : 0 < ell)
    (w : IntegerCliqueWeights d ell)
    (T : Finset (Fin d))
    (U : IntegerGraphSupport d ell) :
    integerCliqueOnSupport (trackFZeroOutside d ell hell w T) U ≤
      integerCliqueOnSupport w U := by
  classical
  unfold integerCliqueOnSupport
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ T
  · simp [trackFZeroOutside,hj]
  · simp [trackFZeroOutside,hj]

/-- On a support entirely within T, zeroing weights outside T
preserves the exact labelled clique multiplicity. -/
theorem trackFZeroOutside_T_mass
    (d ell : Nat) (hell : 0 < ell)
    (w : IntegerCliqueWeights d ell)
    (T : Finset (Fin d))
    (U : IntegerGraphSupport d ell)
    (hUT : U.1 ⊆ T) :
    integerCliqueOnSupport (trackFZeroOutside d ell hell w T) U =
      integerCliqueOnSupport w U := by
  classical
  unfold integerCliqueOnSupport
  apply Finset.sum_congr rfl
  intro j hj
  simp [trackFZeroOutside,hUT hj]

/-- In a full old support V, the zeroed vector's mass is precisely
the ORIGINAL vector's mass on the intersection V∩T. This identity
includes the empty intersection and avoids constructing an invalid
empty IntegerGraphSupport. -/
theorem trackFZeroOutside_inter_sum
    (d ell : Nat) (hell : 0 < ell)
    (w : IntegerCliqueWeights d ell)
    (T : Finset (Fin d))
    (V : IntegerGraphSupport d ell) :
    integerCliqueOnSupport (trackFZeroOutside d ell hell w T) V =
      (V.1 ∩ T).sum (fun j => (w.1 j).val) := by
  classical
  unfold integerCliqueOnSupport
  calc
    V.1.sum (fun j =>
        ((trackFZeroOutside d ell hell w T).1 j).val) =
      (V.1 ∩ T).sum (fun j =>
        ((trackFZeroOutside d ell hell w T).1 j).val) := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro j hjV hjNot
      have hjNotT : j ∉ T := by
        intro hjT
        exact hjNot (Finset.mem_inter.mpr ⟨hjV,hjT⟩)
      simp [trackFZeroOutside,hjNotT]
    _ = (V.1 ∩ T).sum (fun j => (w.1 j).val) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [trackFZeroOutside,(Finset.mem_inter.mp hj).2]

/-- One-directional transfer: B-feasible normalized clique
multiplicities supported within T are C-feasible whenever C is
raw-support-monotone and B,C agree on every support U⊆T.
The proof checks *every* support V of the original full domain. -/
theorem trackFZeroOutside_feasible_of_agree
    (d ell : Nat) (hell : 0 < ell)
    (B C : IntegerGraphSupport d ell → Nat)
    (hCMono : TrackFRawSupportMonotone d ell C)
    (T : IntegerGraphSupport d ell)
    (hAgree : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → B U = C U)
    (w : IntegerCliqueWeights d ell)
    (hB : WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w) :
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell))
      C (trackFZeroOutside d ell hell w T.1) := by
  classical
  intro V
  rw [trackFZeroOutside_inter_sum]
  let Q : Finset (Fin d) := V.1 ∩ T.1
  by_cases hQ : Q.Nonempty
  · let R : IntegerGraphSupport d ell :=
      ⟨Q, ⟨hQ,
        (Finset.card_le_card
          (Finset.inter_subset_left)).trans V.2.2⟩⟩
    calc
      Q.sum (fun j => (w.1 j).val) =
          integerCliqueOnSupport w R := rfl
      _ ≤ B R := hB R
      _ = C R := hAgree R (Finset.inter_subset_right)
      _ ≤ C V := hCMono R V (Finset.inter_subset_left)
  · have hEmpty : Q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hQ
    simp [Q,hEmpty]

/-- FINITE RAW-SUPPORT DELETION LOCALITY:
Monotone raw records B,C that agree on every nonempty support inside
T have exactly the same canonical T-value, independently of ALL
different raw constraints outside T. No 'B is an age' hypothesis.

This is the essential same-index graph-age bridge needed before
changing coordinates from Fin d to the surviving Fin (d-1). -/
theorem trackFCanonical_locality_of_monotone
    (d ell : Nat) (hell : 0 < ell)
    (B C : IntegerGraphSupport d ell → Nat)
    (hBMono : TrackFRawSupportMonotone d ell B)
    (hCMono : TrackFRawSupportMonotone d ell C)
    (T : IntegerGraphSupport d ell)
    (hAgree : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → B U = C U) :
    integerGraphAgeCanonical d ell B T =
      integerGraphAgeCanonical d ell C T := by
  classical
  have hOneWay
      (P Q : IntegerGraphSupport d ell → Nat)
      (hQMono : TrackFRawSupportMonotone d ell Q)
      (hPQ : ∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ T.1 → P U = Q U) :
      integerGraphAgeCanonical d ell P T ≤
        integerGraphAgeCanonical d ell Q T := by
    let value := integerCliqueOnSupport (d := d) (ell := ell)
    change (Finset.univ.filter (WitnessRespects value P)).sup
      (fun w => value w T) ≤
      integerGraphAgeCanonical d ell Q T
    apply Finset.sup_le
    intro w hw
    have hwP : WitnessRespects value P w :=
      (Finset.mem_filter.mp hw).2
    let wt : IntegerCliqueWeights d ell :=
      trackFZeroOutside d ell hell w T.1
    have hwtQ : WitnessRespects value Q wt :=
      trackFZeroOutside_feasible_of_agree
        d ell hell P Q hQMono T hPQ w hwP
    have hTmass : value wt T = value w T :=
      trackFZeroOutside_T_mass d ell hell w T.1 T (subset_rfl)
    calc
      value w T = value wt T := hTmass.symm
      _ ≤ integerGraphAgeCanonical d ell Q T :=
        witnessValue_le_canonical value Q wt hwtQ T
  apply Nat.le_antisymm
  · exact hOneWay B C hCMono hAgree
  · exact hOneWay C B hBMono
      (fun U hUT => (hAgree U hUT).symm)

/-- Actual literal concrete-word histories instantiate the locality
theorem: if two chronological histories have identical raw values on
all admissible nonempty supports inside T, their canonical T-value
is identical. Both support-monotonicity hypotheses are now
derived from genuine word columns, not assumed. -/
theorem trackFWordRaw_locality
    (d ell : Nat) (hell : 0 < ell)
    (A B : List (Fin d → Nat))
    (T : IntegerGraphSupport d ell)
    (hAgree : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 →
      trackFWordRaw d ell A U = trackFWordRaw d ell B U) :
    integerGraphAgeCanonical d ell (trackFWordRaw d ell A) T =
      integerGraphAgeCanonical d ell (trackFWordRaw d ell B) T := by
  exact trackFCanonical_locality_of_monotone d ell hell
    (trackFWordRaw d ell A) (trackFWordRaw d ell B)
    (fun U V hUV => trackFWordRaw_monotone A U V hUV)
    (fun U V hUV => trackFWordRaw_monotone B U V hUV)
    T hAgree

end Kk
