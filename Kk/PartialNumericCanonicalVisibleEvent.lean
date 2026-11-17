import Kk.PartialNumericCanonicalEventWitness
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track A: EXACT visibility criterion for genuine canonical ordinary-L age changes

English proof and 17 hostile checks committed BEFORE Lean:
  docs/partial_numeric_canonical_visible_event_english_audit.md

When raw support bounds Bnew <= Bold, their canonical integer-witness
graph ages differ IFF some bounded normalized clique-multiplicity
vector respects ALL old constraints but fails a new one.

For the actual numerical-H ordinary-L old age across partial cuts,
the physical raw event is a ONE-UNIT fall. Therefore a canonical
change occurs IFF some old-feasible normalized vector SATURATES
a physical support at a cut which crosses that support's one-jump
threshold with current-original eligibility, maximum original
linked capacity and no truncated-subtraction saturation.

This does NOT assert a canonical age COVER or an auxiliary
parameter-closed Kpt E/(I1)--(I3)/(B3) event, nor a global
resolved-copy diary, labelled source orbit or BRD number.
-/

namespace Kk

open SuccessorTree.V10

/-- The canonical integer graph ages of comparable raw bounds
differ precisely when a bounded normalized clique multiplicity
vector is FEASIBLE under every old raw support bound but fails
at least one new one.

No raw positivity or genuine-age hypothesis is required: the
finite canonicalizer is literally the supremum of all normalized
vectors respecting its raw constraints. -/
theorem integerGraphAgeCanonical_ne_iff_lost_clique_vector
    (d ell : Nat)
    (Bnew Bold : IntegerGraphSupport d ell → Nat)
    (hMono : ∀ U, Bnew U ≤ Bold U) :
    integerGraphAgeCanonical d ell Bnew ≠
      integerGraphAgeCanonical d ell Bold ↔
    ∃ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) Bold w ∧
      ¬ WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) Bnew w := by
  classical
  constructor
  · intro hDifferent
    by_contra hNo
    have hFeasibleEq :
        ∀ w : IntegerCliqueWeights d ell,
          WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := ell)) Bnew w ↔
          WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := ell)) Bold w := by
      intro w
      constructor
      · intro hw U
        exact (hw U).trans (hMono U)
      · intro hw
        by_contra hNotNew
        exact hNo ⟨w,hw,hNotNew⟩
    have hSetEq :
        ((Finset.univ : Finset (IntegerCliqueWeights d ell)).filter
          (WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := ell)) Bnew)) =
        ((Finset.univ : Finset (IntegerCliqueWeights d ell)).filter
          (WitnessRespects
            (integerCliqueOnSupport (d := d) (ell := ell)) Bold)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hFeasibleEq w
    apply hDifferent
    funext U
    unfold integerGraphAgeCanonical finiteWitnessCanonical
    rw [hSetEq]
  · rintro ⟨w,hOld,hLost⟩ hSame
    have hOldCan :
        WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell Bold) w :=
      (integerGraphAgeCanonical_preserves_clique_vectors
        d ell Bold w).2 hOld
    have hNewCan :
        WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell Bnew) w := by
      rw [hSame]
      exact hOldCan
    exact hLost
      ((integerGraphAgeCanonical_preserves_clique_vectors
        d ell Bnew w).1 hNewCan)

/-- An ACTUAL canonical ordinary-L partial old-age change is
equivalent to an OLD-feasible normalized integer clique vector
that SATURATES a support U whose TRUE raw bound then falls.

The saturating conclusion relies crucially on the independently
verified physical event being a one-unit fall; without it an
arbitrary lost vector need not saturate the earlier bound. -/
theorem finiteNumericH_partial_canonical_change_iff_saturating_raw_event
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (ell k b g h M : Nat) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b h M j) ≠
    integerGraphAgeCanonical d ell
      (finiteNumericHPhysicalPartialOldRaw E ell k b g M j) ↔
    ∃ w : IntegerCliqueWeights d ell,
    ∃ U : IntegerGraphSupport d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (finiteNumericHPhysicalPartialOldRaw E ell k b g M j) w ∧
      integerCliqueOnSupport w U =
        finiteNumericHPhysicalPartialOldRaw E ell k b g M j U ∧
      (∀ t ∈ U.1, E b (j t) = true) ∧
      finiteDirectedCliqueCapacity E
        ((oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1).filter
          (fun i => E i b = true)) =
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      g ≤ finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < h ∧
      finiteDirectedCliqueCapacity E
        (oldSupportCommonNeighbourPool (Finset.range b)
          (fun i t => E i (j t)) U.1) < ell-1 := by
  classical
  let New := finiteNumericHPhysicalPartialOldRaw E ell k b h M j
  let Old := finiteNumericHPhysicalPartialOldRaw E ell k b g M j
  have hMono : ∀ U : IntegerGraphSupport d ell, New U ≤ Old U := by
    intro U
    exact finiteNumericH_partial_actual_raw_age_antitone
      E ell k b M g h hgh j U
  have hLost :=
    integerGraphAgeCanonical_ne_iff_lost_clique_vector
      d ell New Old hMono
  constructor
  · intro hDifferent
    obtain ⟨w,hOld,hLostNew⟩ := hLost.mp hDifferent
    have hNotAll :
        ¬ ∀ U : IntegerGraphSupport d ell,
          integerCliqueOnSupport w U ≤ New U := hLostNew
    obtain ⟨U,hFail⟩ := Classical.not_forall.mp hNotAll
    have hOldBound := hOld U
    have hStrict : New U < Old U := by omega
    have hCriterion :=
      (finiteNumericH_partial_actual_raw_support_event_iff
        E hSym ell k b g h M hgh hh j hj U).1 hStrict
    have hUnit :
        Old U = New U + 1 :=
      finiteNumericH_partial_actual_raw_support_event_unit
        E hSym ell k b g h M hgh hh j hj U hStrict
    have hSaturates : integerCliqueOnSupport w U = Old U := by
      omega
    exact ⟨w,U,hOld,hSaturates,hCriterion⟩
  · rintro ⟨w,U,hOld,hSat,hEligible,hCapacity,hCut,hLater,hPositive⟩
    have hStrict : New U < Old U :=
      (finiteNumericH_partial_actual_raw_support_event_iff
        E hSym ell k b g h M hgh hh j hj U).2
          ⟨hEligible,hCapacity,hCut,hLater,hPositive⟩
    have hUnit : Old U = New U + 1 :=
      finiteNumericH_partial_actual_raw_support_event_unit
        E hSym ell k b g h M hgh hh j hj U hStrict
    have hNotNew :
        ¬ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) New w := by
      intro hNew
      have hAt := hNew U
      have hImpossible : New U + 1 ≤ New U := by
        calc
          New U + 1 = Old U := hUnit.symm
          _ = integerCliqueOnSupport w U := hSat.symm
          _ ≤ New U := hAt
      omega
    exact hLost.mpr ⟨w,hOld,hNotNew⟩

#print axioms Kk.integerGraphAgeCanonical_ne_iff_lost_clique_vector
#print axioms Kk.finiteNumericH_partial_canonical_change_iff_saturating_raw_event

end Kk
