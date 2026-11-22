import Kk.CanonicalCriticalSlack
import Kk.PreservedTypedNeutralGap
import Mathlib.Tactic

/-!
# Track B: physical Henson covers after a canonically neutral positive interval

English mathematical proof and hostile audit were committed FIRST in
`docs/track_b_canonical_slack_english_audit_20261122.md`.

The old zero-critical-count requirement is replaced by its exact weaker
all-support canonical-slack budget. Every genuine intervening original may
have POSITIVE typed columns. The original graph E and every old column are
unchanged. The result constructs one genuine later reserved clique, and
maintains an earlier actual finite stage as a separate certificate.

It does NOT construct the selected witnesses nor identify the distinct
finite numerical-H embeddings, and does NOT prove dependent Kpt/I1-I3/B3
or a common labelled inverse-source orbit.
-/

namespace Kk

/-- The existing real Henson one-cover construction can start beyond an
arbitrary finite interval of possibly positive selected/parameter originals,
provided the full critical counts on every admissible support fit the RAW
slack of the genuine old canonical age.

At every intermediate original cut the ordinary canonical age is unchanged. -/
theorem henson_leftDense_physical_cover_after_canonical_slack_interval
    (d ell b m k r : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (lower middle : IntegerGraphSupport d ell → Nat)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = middle)
    (hSlack : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m + middle U ≤
        finiteOldColumnRawBound E ell d (Finset.range b) c U)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll : ell = lower T + r + 1)
    (hAt : middle T = lower T + 1) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, b+m ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < b+m → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn (b+m) Q T.1 c)) = lower ∧
      HasUniformPositiveSupportStage E d ell (b+m) F k hd c Q T ∧
      (∀ j, j ≤ m →
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c) = middle) := by
  classical
  have hOldAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)) := by
    rw [hPrior]
    exact hCover.upper_age
  have hFullBudget : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m +
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) U ≤
      finiteOldColumnRawBound E ell d (Finset.range b) c U := by
    intro U
    simpa only [hPrior] using hSlack U
  have hNeutral : integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) :=
    (integerGraphAgeCanonical_interval_eq_iff_critical_slack
      E ell d b m c hOldAge).2 hFullBudget
  have hAtEnd : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
        middle := hNeutral.trans hPrior
  obtain ⟨Q,F,hCard,hWithin,hClique,hIso,hAge,_hFeasible,hStage⟩ :=
    henson_leftDense_exists_physical_finite_canonical_cover_stage
      d ell (b+m) k r hell hd E hAvoid hDense c T
      lower middle hCover hEll hAt hAtEnd
  refine ⟨Q,F,hCard,hWithin,hClique,hIso,hAge,hStage,?_⟩
  intro j hj
  have hIntermediate :=
    integerGraphAgeCanonical_every_intermediate_eq_of_critical_slack
      E ell d b m c hOldAge hFullBudget j hj
  exact hIntermediate.trans hPrior

/-- A second true physical cover after ACTUAL committed selected/parameter
original images W0: their complete columns (even POSITIVE ones) are preserved.

The first finite numerical-H stage is retained only as its own existential
certificate; no common f,M or dependent upper Kpt source is inferred. -/
theorem henson_leftDense_second_cover_after_preserved_typed_slack_interval
    (d ell b F0 m k0 k1 r1 : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c cNext : Nat → Fin d → Bool)
    (Q0 W0 : Finset Nat)
    (T0 T1 : IntegerGraphSupport d ell)
    (lower middle : IntegerGraphSupport d ell → Nat)
    (hQ0Within : ∀ q ∈ Q0, b ≤ q ∧ q < F0)
    (hFirstStage : HasUniformPositiveSupportStage
      E d ell b F0 k0 hd c Q0 T0)
    (hFirstAge : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range F0)
        (supportBlockGappedColumn b Q0 T0.1 c)) = middle)
    (hNextPrefix : ∀ p, p < F0 → ∀ t,
      cNext p t = supportBlockGappedColumn b Q0 T0.1 c p t)
    (hWBefore : ∀ w ∈ W0, w < F0+m)
    (hSlack : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d F0 cNext U m + middle U ≤
        finiteOldColumnRawBound E ell d (Finset.range F0) cNext U)
    (hCover1 : AgeCover (IsIntegerGraphAge d ell) lower middle)
    (hEll1 : ell = lower T1 + r1 + 1)
    (hAt1 : middle T1 = lower T1 + 1) :
    ∃ (Q1 : Finset Nat) (F1 : Nat),
      Q1.card = r1 ∧
      (∀ q ∈ Q1, F0+m ≤ q ∧ q < F1) ∧
      IsDirectedCliqueOn E Q1 ∧
      (∀ p, p < F0+m → ∀ q ∈ Q1,
        E p q = false ∧ E q p = false) ∧
      (∀ q0 ∈ Q0, ∀ q1 ∈ Q1,
        E q0 q1 = false ∧ E q1 q0 = false) ∧
      (∀ w ∈ W0, ∀ q ∈ Q1,
        E w q = false ∧ E q w = false) ∧
      (∀ p, p < F0+m → ∀ t : Fin d,
        supportBlockGappedColumn (F0+m) Q1 T1.1 cNext p t =
          cNext p t) ∧
      (∀ w ∈ W0, ∀ t : Fin d,
        supportBlockGappedColumn (F0+m) Q1 T1.1 cNext w t =
          cNext w t) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F1)
          (supportBlockGappedColumn (F0+m) Q1 T1.1 cNext)) = lower ∧
      (∀ j, j ≤ m →
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range (F0+j)) cNext) = middle) ∧
      HasUniformPositiveSupportStage E d ell b F0 k0 hd c Q0 T0 ∧
      HasUniformPositiveSupportStage E d ell (F0+m) F1 k1 hd cNext Q1 T1 := by
  classical
  have hNextAge : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range F0) cNext) = middle :=
    (integerGraphAgeCanonical_eq_of_column_prefix E ell d F0
      cNext (supportBlockGappedColumn b Q0 T0.1 c)
      hNextPrefix).trans hFirstAge
  obtain ⟨Q1,F1,hCard,hWithin,hClique,hIso,hAge,hSecondStage,hNeutral⟩ :=
    henson_leftDense_physical_cover_after_canonical_slack_interval
      d ell F0 m k1 r1 hell hd E hAvoid hDense cNext T1
      lower middle hNextAge hSlack hCover1 hEll1 hAt1
  refine ⟨Q1,F1,hCard,hWithin,hClique,hIso,?_,?_,?_,?_,
    hAge,hNeutral,hFirstStage,hSecondStage⟩
  · intro q0 hq0 q1 hq1
    have hq0Before : q0 < F0+m := by
      have hq0F := (hQ0Within q0 hq0).2
      omega
    exact hIso q0 hq0Before q1 hq1
  · intro w hw q hq
    exact hIso w (hWBefore w hw) q hq
  · intro p hp t
    exact supportBlockGappedColumn_eq_before_cut
      (F0+m) Q1 T1.1 cNext
      (fun q hq => (hWithin q hq).1) p hp t
  · intro w hw t
    exact supportBlockGappedColumn_eq_before_cut
      (F0+m) Q1 T1.1 cNext
      (fun q hq => (hWithin q hq).1)
      w (hWBefore w hw) t

#print axioms Kk.henson_leftDense_physical_cover_after_canonical_slack_interval
#print axioms Kk.henson_leftDense_second_cover_after_preserved_typed_slack_interval

end Kk
