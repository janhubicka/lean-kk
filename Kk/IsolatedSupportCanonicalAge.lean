import Kk.IsolatedSupportBlockRawAge
import Kk.FiniteSupportCoverProfile
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# KK Track A: actual isolated reserved raw age = ideal cover AFTER canonicalization

English mathematical proof and hostile audit committed BEFORE this file:
  docs/isolated_support_canonical_age_english_audit.md

The literal physical raw bound after inserting an isolated Q with
complete support-T columns changes at EVERY U⊆T, including proper
sub-supports. It is generally NOT pointwise equal to the ideal
single-coordinate rawCliqueBlockBound ell (cap Q) B T.

This module proves that their entire normalized integer witness
families are EXACTLY equal and consequently their canonical integer
graph-age functions are POINTWISE EQUAL. It needs no positivity
assumption or unverified physical existence axiom. With the old
canonical reference age=upper and a genuine integer age cover,
the already kernel-checked canonical cover-block theorem supplies
the exact upper/lower age update at the literal reserved capacity.

This is a finite ordinary-L calculation. The coherent infinite
resolved diary, H+ auxiliary Kpt E / parameter-closed B3 and
common labelled inverse-source orbit remain independent.
-/

namespace Kk

/-- The whole witness system of the ACTUAL isolated support-T
reserved block is the complete OLD raw system together with the
single extra total T-count threshold ell-1-cap_E(Q).

This does not claim pointwise equality of raw functions. The
proof uses the old raw-age monotonicity and exact max-capacity
formula from the verified physical isolated-block theorem, plus
nonnegative multiplicities on every proper U⊆T. -/
theorem isolatedSupportWitnessRespects_iff_old_and_threshold
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (finiteOldColumnRawBound E ell d (P ∪ Q)
        (supportBlockOldColumn Q T.1 c)) w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        (finiteOldColumnRawBound E ell d P c) w ∧
      integerCliqueOnSupport w T ≤
        ell - 1 - finiteDirectedCliqueCapacity E Q := by
  classical
  let a : Nat := finiteDirectedCliqueCapacity E Q
  let B : IntegerGraphSupport d ell → Nat :=
    finiteOldColumnRawBound E ell d P c
  constructor
  · intro hNew
    have hOld :
        WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
      intro U
      exact (hNew U).trans
        (supportBlockRawBound_le_old E ell d P Q hDisjoint
          hZero c T U)
    have hT := hNew T
    rw [supportBlockRawBound_exact
      E ell d P Q hDisjoint hZero c T T] at hT
    simp only [if_pos (Finset.Subset.refl T.1)] at hT
    have haLe : a ≤ max
        (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c T.1)) a :=
      le_max_right _ _
    have hThreshold : integerCliqueOnSupport w T ≤ ell - 1 - a := by
      omega
    exact ⟨hOld, hThreshold⟩
  · rintro ⟨hOld,hT⟩ U
    have hExact := supportBlockRawBound_exact
      E ell d P Q hDisjoint hZero c T U
    rw [hExact]
    by_cases hSubset : U.1 ⊆ T.1
    · simp only [if_pos hSubset]
      have hSum : integerCliqueOnSupport w U ≤
          integerCliqueOnSupport w T := by
        change U.1.sum (fun t : Fin d => (w.1 t).val) ≤
          T.1.sum (fun t : Fin d => (w.1 t).val)
        exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
          (by intro t _ _; exact Nat.zero_le _)
      have hOldU : integerCliqueOnSupport w U ≤
          ell - 1 - finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool P c U.1) := hOld U
      have hA : integerCliqueOnSupport w U ≤ ell - 1 - a :=
        hSum.trans hT
      rcases le_total
        (finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool P c U.1)) a with hRho | hCap
      · rw [max_eq_right hRho]
        exact hA
      · rw [max_eq_left hCap]
        exact hOldU
    · simp only [if_neg hSubset]
      exact hOld U

/-- EXACT whole-constraint meaning of the ideal raw cover block:
all original raw support bounds plus a single T-count threshold.
No positivity or capacity a<ell hypothesis is needed for this
pure statement about the normalized witness multiplicities. -/
theorem integerWitnessRespects_rawCliqueBlock_iff
    (d ell a : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (rawCliqueBlockBound ell a B T) w ↔
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      B w ∧
    integerCliqueOnSupport w T ≤ ell - 1 - a := by
  classical
  constructor
  · intro hBlock
    have hOld :
        WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
      intro U
      exact (hBlock U).trans
        (rawCliqueBlockBound_le_upper ell a B T U)
    have hAt := hBlock T
    have hEq : rawCliqueBlockBound ell a B T T =
        min (B T) (ell - 1 - a) := by
      simp [rawCliqueBlockBound]
    rw [hEq] at hAt
    exact ⟨hOld, hAt.trans (Nat.min_le_right _ _)⟩
  · rintro ⟨hOld,hAt⟩ U
    by_cases hSame : U = T
    · subst U
      have hBound : integerCliqueOnSupport w T ≤
          min (B T) (ell - 1 - a) :=
        le_min (hOld T) hAt
      simpa [rawCliqueBlockBound] using hBound
    · simpa [rawCliqueBlockBound, hSame] using (hOld U)

/-- ACTUAL and IDEAL raw reserved-block functions are not usually
pointwise equal. Nonetheless each normalized integer witness
satisfies ALL support bounds of one exactly when it satisfies
ALL support bounds of the other. -/
theorem isolatedSupportWitnessRespects_iff_ideal
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (finiteOldColumnRawBound E ell d (P ∪ Q)
        (supportBlockOldColumn Q T.1 c)) w ↔
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (rawCliqueBlockBound ell
        (finiteDirectedCliqueCapacity E Q)
        (finiteOldColumnRawBound E ell d P c) T) w := by
  exact
    (isolatedSupportWitnessRespects_iff_old_and_threshold
      E ell d P Q hDisjoint hZero c T w).trans
    (integerWitnessRespects_rawCliqueBlock_iff
      d ell (finiteDirectedCliqueCapacity E Q)
      (finiteOldColumnRawBound E ell d P c) T w).symm

/-- General reusable principle: two raw functions that admit
EXACTLY the same normalized integer witnesses have identical
canonical integer graph-age functions POINTWISE. -/
theorem integerGraphAgeCanonical_eq_of_respects_iff
    (d ell : Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (hWitness : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        B w ↔
      WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
        C w) :
    integerGraphAgeCanonical d ell B =
      integerGraphAgeCanonical d ell C := by
  classical
  have hSet :
      (Finset.univ.filter
        (WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) B) :
            Finset (IntegerCliqueWeights d ell)) =
      (Finset.univ.filter
        (WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) C) :
            Finset (IntegerCliqueWeights d ell)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hWitness w
  funext U
  change
    (Finset.univ.filter
      (WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B) :
          Finset (IntegerCliqueWeights d ell)).sup
            (fun w => integerCliqueOnSupport w U) =
    (Finset.univ.filter
      (WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) C) :
          Finset (IntegerCliqueWeights d ell)).sup
            (fun w => integerCliqueOnSupport w U)
  rw [hSet]

/-- The strongest correct equality: the canonical graph age of the
REAL isolated Q insertion is IDENTICAL to canonicalization of
the IDEAL one-coordinate raw cover block, at EVERY support.
The underlying RAW functions may differ on proper U⊊T. -/
theorem isolatedSupportCanonicalAge_eq_ideal
    (E : Nat → Nat → Bool) (ell d : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (P ∪ Q)
        (supportBlockOldColumn Q T.1 c)) =
    integerGraphAgeCanonical d ell
      (rawCliqueBlockBound ell
        (finiteDirectedCliqueCapacity E Q)
        (finiteOldColumnRawBound E ell d P c) T) := by
  apply integerGraphAgeCanonical_eq_of_respects_iff
  intro w
  exact isolatedSupportWitnessRespects_iff_ideal
    E ell d P Q hDisjoint hZero c T w

/-- Raw ideal cover canonicalization depends on B only through the
full witness-feasibility system of its canonicalized age G_B,
not through pointwise equality B=G_B. -/
theorem integerGraphAgeCanonical_idealBlock_congr
    (d ell a : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell) :
    integerGraphAgeCanonical d ell
      (rawCliqueBlockBound ell a B T) =
    integerGraphAgeCanonical d ell
      (rawCliqueBlockBound ell a
        (integerGraphAgeCanonical d ell B) T) := by
  apply integerGraphAgeCanonical_eq_of_respects_iff
  intro w
  have hLeft := integerWitnessRespects_rawCliqueBlock_iff
    d ell a B T w
  have hRight := integerWitnessRespects_rawCliqueBlock_iff
    d ell a (integerGraphAgeCanonical d ell B) T w
  constructor
  · intro h
    obtain ⟨hB,hAt⟩ := hLeft.mp h
    apply hRight.mpr
    exact ⟨(integerGraphAgeCanonical_preserves_clique_vectors
      d ell B w).mpr hB,hAt⟩
  · intro h
    obtain ⟨hCanonical,hAt⟩ := hRight.mp h
    apply hLeft.mpr
    exact ⟨(integerGraphAgeCanonical_preserves_clique_vectors
      d ell B w).mp hCanonical,hAt⟩

/-- If the actual PRE-block canonical age is the designated upper
member of a genuine integer graph-age cover, the literal new
old-column canonical age is EXACTLY upper before reserved
capacity r, and lower at capacity r.

This calculation uses the TRUE physical raw age of P∪Q. It does
NOT identify that raw function pointwise with an ideal block, and
does not assume the unbounded selected stage actually exists. -/
theorem isolatedSupportCanonicalAge_cover_step
    (E : Nat → Nat → Bool) (ell d r : Nat)
    (P Q : Finset Nat) (hDisjoint : Disjoint P Q)
    (hZero : ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d P c) = upper)
    (hCap : finiteDirectedCliqueCapacity E Q ≤ r) :
    integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (P ∪ Q)
        (supportBlockOldColumn Q T.1 c)) =
      if finiteDirectedCliqueCapacity E Q < r then upper else lower := by
  rw [isolatedSupportCanonicalAge_eq_ideal
    E ell d P Q hDisjoint hZero c T]
  rw [integerGraphAgeCanonical_idealBlock_congr d ell
    (finiteDirectedCliqueCapacity E Q)
    (finiteOldColumnRawBound E ell d P c) T]
  rw [hPrior]
  exact integerGraphAge_canonical_cover_block d ell r
    lower upper T hCover hEll hAt
    (finiteDirectedCliqueCapacity E Q) hCap

#print axioms Kk.isolatedSupportWitnessRespects_iff_old_and_threshold
#print axioms Kk.integerWitnessRespects_rawCliqueBlock_iff
#print axioms Kk.isolatedSupportWitnessRespects_iff_ideal
#print axioms Kk.integerGraphAgeCanonical_eq_of_respects_iff
#print axioms Kk.isolatedSupportCanonicalAge_eq_ideal
#print axioms Kk.integerGraphAgeCanonical_idealBlock_congr
#print axioms Kk.isolatedSupportCanonicalAge_cover_step

end Kk
