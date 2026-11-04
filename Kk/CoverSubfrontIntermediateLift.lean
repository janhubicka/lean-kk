import Kk.CanonicalCoverEventLocality
import Mathlib.Tactic

/-!
# A genuine graph-age cover restricts to a cover or equality on ANY subfront

ENGLISH proof and 11-item hostile mathematical audit were committed FIRST
in `docs/cover_subfront_lift_english_audit.md` BEFORE this source.

A graph age on an arbitrary finite subset E of the selected front is
represented by actual normalized integer clique multiplicity witnesses
supported INSIDE E, with bounds only on eligible nonempty supports S⊆E.

Given any such intermediate relative age H between the restrictions
of a full genuine cover lower ⋖ upper, form the MIXED RAW bound:
  B(S)=H(S) if S⊆E; B(S)=upper(S) otherwise.
The actual integer-witness canonical age G_B is sandwiched between lower
and upper. A relative H witness extended by zero outside E satisfies ALL
raw B bounds: on supports U not inside E, use Q=U∩E; the Q=empty case
requires a separate zero-sum argument. Therefore G_B restricts to H.
Cover minimality forces G_B=lower or G_B=upper, and thus H is one endpoint.

Consequently any genuine cover of finite integer-witness graph ages
restricts to equality or a genuine cover on EVERY subfront, including
those CONTAINING the distinguished changed support. This is a genuine
cover MACRO-event algebra statement, NOT the physical numerical-H
reserved-original realization or equality of full dependent I1/I2/I3/B3
source types and one labelled inverse-source orbit.
-/

namespace Kk

/-- True integer-witness graph age on the selected subfront E.
The total function H is inspected ONLY on supports S⊆E; outside
E its values are immaterial. Every saturating witness is an
actual finite normalized integer vector supported inside E. -/
def IsSubfrontIntegerGraphAge
    (d ell : Nat) (E : Finset (Fin d))
    (H : IntegerGraphSupport d ell → Nat) : Prop :=
  (∀ S : IntegerGraphSupport d ell,
    S.1 ⊆ E → 1 ≤ H S ∧ H S ≤ ell-1) ∧
  (∀ S : IntegerGraphSupport d ell,
    S.1 ⊆ E →
    ∃ w : IntegerCliqueWeights d ell,
      (∀ j : Fin d, j ∉ E → (w.1 j).val = 0) ∧
      (∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ E → integerCliqueOnSupport w U ≤ H U) ∧
      integerCliqueOnSupport w S = H S)

/-- A genuine full integer-witness age restricts to a genuine
relative age on ANY finite subfront E, not just initial segments.
We construct its witness by ZEROING every coordinate outside E. -/
theorem integerGraphAge_is_subfront_age
    (d ell : Nat) (hell : 0 < ell)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (E : Finset (Fin d)) :
    IsSubfrontIntegerGraphAge d ell E F := by
  classical
  constructor
  · intro S _
    exact hAge.1 S
  · intro S hSE
    obtain ⟨w, hBounds, hValue⟩ := hAge.2 S
    let zero : Fin ell := ⟨0, hell⟩
    let wE : Fin d → Fin ell :=
      fun j => if j ∈ E then w.1 j else zero
    have hTotalLe :
        Finset.univ.sum (fun j : Fin d => (wE j).val) ≤
          Finset.univ.sum (fun j : Fin d => (w.1 j).val) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ E
      · simp [wE, hj]
      · simp [wE, hj, zero]
    let wn : IntegerCliqueWeights d ell :=
      ⟨wE, hTotalLe.trans w.2⟩
    refine ⟨wn, ?_, ?_, ?_⟩
    · intro j hj
      simp [wn, wE, hj, zero]
    · intro U hUE
      have hEq :
          integerCliqueOnSupport wn U =
            integerCliqueOnSupport w U := by
        unfold integerCliqueOnSupport
        apply Finset.sum_congr rfl
        intro j hjU
        have hjE : j ∈ E := hUE hjU
        simp [wn, wE, hjE]
      rw [hEq]
      exact hBounds U
    · calc
        integerCliqueOnSupport wn S =
          integerCliqueOnSupport w S := by
            unfold integerCliqueOnSupport
            apply Finset.sum_congr rfl
            intro j hjS
            have hjE : j ∈ E := hSE hjS
            simp [wn, wE, hjE]
        _ = F S := hValue

/-- Mixed RAW bound of a relative age H on E with the genuine
ambient upper graph age outside E. This raw table is NOT assumed
to be an age: the canonicalizer will repair any inconsistencies. -/
noncomputable def subfrontMixedRawBound
    (d ell : Nat) (E : Finset (Fin d))
    (H upper : IntegerGraphSupport d ell → Nat) :
    IntegerGraphSupport d ell → Nat := by
  classical
  exact fun S => if S.1 ⊆ E then H S else upper S

/-- The mixed raw table is sandwiched between genuine lower and
upper ages when the relative H lies between their E-restrictions. -/
theorem subfrontMixedRawBound_between
    (d ell : Nat) (E : Finset (Fin d))
    (lower upper H : IntegerGraphSupport d ell → Nat)
    (hGlobal : AgeLe lower upper)
    (hRelativeLow : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S ≤ H S)
    (hRelativeHigh : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S ≤ upper S) :
    AgeLe lower (subfrontMixedRawBound d ell E H upper) ∧
      AgeLe (subfrontMixedRawBound d ell E H upper) upper := by
  constructor
  · intro S
    by_cases hSE : S.1 ⊆ E
    · simpa [subfrontMixedRawBound, hSE] using
        hRelativeLow S hSE
    · simpa [subfrontMixedRawBound, hSE] using hGlobal S
  · intro S
    by_cases hSE : S.1 ⊆ E
    · simpa [subfrontMixedRawBound, hSE] using
        hRelativeHigh S hSE
    · simp [subfrontMixedRawBound, hSE]

/-- Key ZERO-SUPPORTED relative witness lemma: a witness satisfying
every relative H-bound INSIDE E also satisfies ALL ambient mixed
raw constraints B, including U NOT contained in E.
When U∩E=empty, the sum is zero rather than an illegal H(empty).
When U∩E is nonempty, use genuine upper-age monotonicity. -/
theorem subfrontWitness_respects_mixed_raw
    (d ell : Nat)
    (E : Finset (Fin d))
    (H upper : IntegerGraphSupport d ell → Nat)
    (hUpperAge : IsIntegerGraphAge d ell upper)
    (hHUpper : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S ≤ upper S)
    (w : IntegerCliqueWeights d ell)
    (hOutside : ∀ j : Fin d, j ∉ E → (w.1 j).val = 0)
    (hRelative : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → integerCliqueOnSupport w S ≤ H S) :
    WitnessRespects (integerCliqueOnSupport (d := d) (ell := ell))
      (subfrontMixedRawBound d ell E H upper) w := by
  classical
  intro U
  by_cases hUE : U.1 ⊆ E
  · simpa [subfrontMixedRawBound, hUE] using hRelative U hUE
  · let Q : Finset (Fin d) := U.1 ∩ E
    have hQsum :
        Q.sum (fun j : Fin d => (w.1 j).val) =
          U.1.sum (fun j : Fin d => (w.1 j).val) := by
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro j hjU hjNotQ
      have hjNotE : j ∉ E := by
        intro hjE
        exact hjNotQ (Finset.mem_inter.mpr ⟨hjU, hjE⟩)
      exact hOutside j hjNotE
    have hRaw : subfrontMixedRawBound d ell E H upper U =
        upper U := by
      simp [subfrontMixedRawBound, hUE]
    rw [hRaw]
    by_cases hQN : Q.Nonempty
    · let V : IntegerGraphSupport d ell :=
        ⟨Q, ⟨hQN,
          (Finset.card_le_card
            (Finset.inter_subset_left)).trans U.2.2⟩⟩
      have hVE : V.1 ⊆ E :=
        Finset.inter_subset_right
      have hVU : V.1 ⊆ U.1 :=
        Finset.inter_subset_left
      calc
        integerCliqueOnSupport w U =
            integerCliqueOnSupport w V := by
          change U.1.sum (fun j : Fin d => (w.1 j).val) =
            Q.sum (fun j : Fin d => (w.1 j).val)
          exact hQsum.symm
        _ ≤ H V := hRelative V hVE
        _ ≤ upper V := hHUpper V hVE
        _ ≤ upper U :=
          integerGraphAge_monotone d ell upper
            hUpperAge V U hVU
    · have hQempty : Q = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hQN
      have hValueZero : integerCliqueOnSupport w U = 0 := by
        unfold integerCliqueOnSupport
        rw [← hQsum, hQempty]
        simp
      rw [hValueZero]
      exact Nat.zero_le _

/-- Main lifting lemma. Canonicalizing the mixed raw table gives
a genuine full ambient age whose restriction on E equals EXACTLY
the arbitrary genuine relative age H, not merely an upper bound.
This is the missing step in the manuscript's cover-subfront proof. -/
theorem integerGraphAgeCanonical_mixed_raw_restrict_eq
    (d ell : Nat) (E : Finset (Fin d))
    (H upper : IntegerGraphSupport d ell → Nat)
    (hRelativeAge : IsSubfrontIntegerGraphAge d ell E H)
    (hUpperAge : IsIntegerGraphAge d ell upper)
    (hHUpper : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S ≤ upper S) :
    ∀ S : IntegerGraphSupport d ell, S.1 ⊆ E →
      integerGraphAgeCanonical d ell
        (subfrontMixedRawBound d ell E H upper) S = H S := by
  classical
  intro S hSE
  apply Nat.le_antisymm
  · calc
      integerGraphAgeCanonical d ell
          (subfrontMixedRawBound d ell E H upper) S ≤
          subfrontMixedRawBound d ell E H upper S :=
        integerGraphAgeCanonical_le_raw d ell _ S
      _ = H S := by
        simp [subfrontMixedRawBound, hSE]
  · obtain ⟨w, hOutside, hBounds, hValue⟩ :=
      hRelativeAge.2 S hSE
    have hwB :=
      subfrontWitness_respects_mixed_raw
        d ell E H upper hUpperAge hHUpper w hOutside hBounds
    calc
      H S = integerCliqueOnSupport w S := hValue.symm
      _ ≤ integerGraphAgeCanonical d ell
          (subfrontMixedRawBound d ell E H upper) S :=
        witnessValue_le_canonical
          (integerCliqueOnSupport (d := d) (ell := ell))
          (subfrontMixedRawBound d ell E H upper) w hwB S

/-- For any genuine full graph-age COVER, there is NO intermediate
genuine relative integer-witness age on ANY selected subfront E.

We do not pretend H is globally consistent: instead we construct its
mixed RAW lift B, canonicalize B using actual finite integer witnesses,
prove the resulting full age lies between lower and upper, and prove
that its restricted age is exactly H. The genuine ambient cover then
forces H to equal one of the two restricted endpoints. -/
theorem integerGraphAge_cover_no_relative_intermediate
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (E : Finset (Fin d))
    (H : IntegerGraphSupport d ell → Nat)
    (hRelativeAge : IsSubfrontIntegerGraphAge d ell E H)
    (hLow : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S ≤ H S)
    (hHigh : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S ≤ upper S) :
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S = lower S) ∨
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S = upper S) := by
  let B := subfrontMixedRawBound d ell E H upper
  let G := integerGraphAgeCanonical d ell B
  have hBbounds :=
    subfrontMixedRawBound_between
      d ell E lower upper H hCover.le hLow hHigh
  have hGLower : AgeLe lower G := by
    exact integerGraphAgeCanonical_greatest
      d ell B lower hCover.lower_age hBbounds.1
  have hGUpper : AgeLe G upper := by
    intro S
    exact (integerGraphAgeCanonical_le_raw d ell B S).trans
      (hBbounds.2 S)
  have hGAge : IsIntegerGraphAge d ell G :=
    integerGraphAgeCanonical_is_age
      d ell B lower hCover.lower_age hBbounds.1
  have hRestricted : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → G S = H S :=
    integerGraphAgeCanonical_mixed_raw_restrict_eq
      d ell E H upper hRelativeAge hCover.upper_age hHigh
  rcases hCover.no_intermediate G hGAge hGLower hGUpper with hEq | hEq
  · left
    intro S hSE
    have hLocal := (hRestricted S hSE).symm
    simpa only [hEq] using hLocal
  · right
    intro S hSE
    have hLocal := (hRestricted S hSE).symm
    simpa only [hEq] using hLocal

/-- A true relative-cover predicate: two genuine relative ages
are comparable, distinct on at least one visible support, and have
NO proper intermediate relative integer-witness age.
Different total functions outside E represent the same relative age. -/
def IsSubfrontIntegerGraphAgeCover
    (d ell : Nat) (E : Finset (Fin d))
    (lower upper : IntegerGraphSupport d ell → Nat) : Prop :=
  IsSubfrontIntegerGraphAge d ell E lower ∧
  IsSubfrontIntegerGraphAge d ell E upper ∧
  (∀ S : IntegerGraphSupport d ell,
    S.1 ⊆ E → lower S ≤ upper S) ∧
  (∃ S : IntegerGraphSupport d ell,
    S.1 ⊆ E ∧ lower S ≠ upper S) ∧
  (∀ H : IntegerGraphSupport d ell → Nat,
    IsSubfrontIntegerGraphAge d ell E H →
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S ≤ H S) →
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S ≤ upper S) →
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S = lower S) ∨
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → H S = upper S))

/-- FULL arbitrary-subfront cover-or-equality result for actual
finite integer-witness K_ell graph ages. This includes subfronts
CONTAINING the changed cover support, not just disjoint ones. -/
theorem integerGraphAge_cover_restrict_eq_or_cover
    (d ell : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (E : Finset (Fin d)) :
    (∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S = upper S) ∨
      IsSubfrontIntegerGraphAgeCover d ell E lower upper := by
  classical
  by_cases hEq : ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S = upper S
  · exact Or.inl hEq
  · right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact integerGraphAge_is_subfront_age
        d ell hell lower hCover.lower_age E
    · exact integerGraphAge_is_subfront_age
        d ell hell upper hCover.upper_age E
    · intro S _
      exact hCover.le S
    · push_neg at hEq
      obtain ⟨S, hSE, hNe⟩ := hEq
      exact ⟨S, hSE, hNe⟩
    · intro H hRel hLow hHigh
      exact integerGraphAge_cover_no_relative_intermediate
        d ell hell lower upper hCover E H hRel hLow hHigh

end Kk
