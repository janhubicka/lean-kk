import Kk.CriticalCountSafeAge
import Kk.TrackFTypePrefixCanonicalAgeSandwich
import Mathlib.Tactic

/-!
# Track B: exact canonical neutrality of a finite positive original interval

English proof and independent adversarial counterexample analysis were committed
FIRST at `docs/track_b_canonical_slack_english_audit_20261122.md`.

For the complete original interval, canonical age is preserved precisely when
the number of critical ORIGINAL insertions consumes no more than the OLD RAW
slack above the genuine initial canonical age, on EVERY supported sort set.
The passing columns of the inserted originals need NOT be zero.

There is no K_ell-freeness assumption on the final prefix for this purely
algebraic finite criterion. The stronger claim that dependent numerical-H+
Kpt/I1-I3/B3 parameter levels are boring does NOT follow.
-/

namespace Kk

/-- If the initial full canonical age is genuine, equality of the canonical
ages across an arbitrary original interval is equivalent to every critical
original count fitting the old RAW slack.

This is strictly weaker than ZERO critical counts; no prior raw=canonical
equality, no singleton-only budget and no extra final-freeness hypothesis. -/
theorem integerGraphAgeCanonical_interval_eq_iff_critical_slack
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c))) :
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) ↔
    ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m +
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) U ≤
      finiteOldColumnRawBound E ell d (Finset.range b) c U := by
  classical
  let B0 := finiteOldColumnRawBound E ell d (Finset.range b) c
  let Bm := finiteOldColumnRawBound E ell d (Finset.range (b+m)) c
  let P := integerGraphAgeCanonical d ell B0
  have hTel (U : IntegerGraphSupport d ell) :
      Bm U = B0 U - originalCriticalCount E ell d b c U m := by
    exact finiteOldColumnRawBound_eq_sub_criticalCount
      E ell d b m c U
  have hRawLe : AgeLe Bm B0 := by
    intro U
    rw [hTel]
    exact Nat.sub_le _ _
  have hCanonLe : AgeLe (integerGraphAgeCanonical d ell Bm) P :=
    integerGraphAgeCanonical_mono_raw d ell Bm B0 hRawLe
  constructor
  · intro hEq U
    have hPos : 1 ≤ P U := (hAge.1 U).1
    have hRaw : P U ≤ Bm U := by
      calc
        P U = integerGraphAgeCanonical d ell Bm U :=
          (congrFun hEq U).symm
        _ ≤ Bm U := integerGraphAgeCanonical_le_raw d ell Bm U
    rw [hTel] at hRaw
    change originalCriticalCount E ell d b c U m + P U ≤ B0 U
    omega
  · intro hBudget
    have hPLeNewRaw : AgeLe P Bm := by
      intro U
      have h := hBudget U
      change originalCriticalCount E ell d b c U m + P U ≤ B0 U at h
      rw [hTel]
      omega
    have hPLeNewCanon : AgeLe P (integerGraphAgeCanonical d ell Bm) :=
      integerGraphAgeCanonical_greatest d ell Bm P hAge hPLeNewRaw
    funext U
    exact Nat.le_antisymm (hCanonLe U) (hPLeNewCanon U)

/-- Exact endpoint canonical slack freezes the entire intermediate ordinary
canonical age at EVERY genuine original index, even when positive columns
are inserted and some RAW support bounds decrease. -/
theorem integerGraphAgeCanonical_every_intermediate_eq_of_critical_slack
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)))
    (hSlack : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m +
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) U ≤
      finiteOldColumnRawBound E ell d (Finset.range b) c U)
    (j : Nat) (hj : j ≤ m) :
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  classical
  have hEnds :
      integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) :=
    (integerGraphAgeCanonical_interval_eq_iff_critical_slack
      E ell d b m c hAge).2 hSlack
  have hStartMid : Finset.range b ⊆ Finset.range (b+j) := by
    intro p hp
    simp only [Finset.mem_range] at hp ⊢
    omega
  have hMidFinal : Finset.range (b+j) ⊆ Finset.range (b+m) := by
    intro p hp
    simp only [Finset.mem_range] at hp ⊢
    omega
  have hRawFinalMid : AgeLe
      (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c)
      (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c) := by
    intro U
    exact finiteOldColumnRawBound_antitone_old_pool E ell d
      (Finset.range (b+j)) (Finset.range (b+m)) c U hMidFinal
  have hRawMidStart : AgeLe
      (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c)
      (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
    intro U
    exact finiteOldColumnRawBound_antitone_old_pool E ell d
      (Finset.range b) (Finset.range (b+j)) c U hStartMid
  have hCanonFinalMid := integerGraphAgeCanonical_mono_raw d ell
    (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c)
    (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c)
    hRawFinalMid
  have hCanonMidStart := integerGraphAgeCanonical_mono_raw d ell
    (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c)
    (finiteOldColumnRawBound E ell d (Finset.range b) c)
    hRawMidStart
  funext U
  apply Nat.le_antisymm (hCanonMidStart U)
  calc
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) U :=
        (congrFun hEnds U).symm
    _ ≤ integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+j)) c) U :=
        hCanonFinalMid U

/-- At a support where the old RAW bound is already CANONICALLY tight,
even one genuine critical original forces an ordinary canonical-age drop. -/
theorem originalCriticalCount_zero_of_canonical_interval_eq_tight
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)))
    (hEq : integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c))
    (U : IntegerGraphSupport d ell)
    (hTight : finiteOldColumnRawBound E ell d (Finset.range b) c U =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) U) :
    originalCriticalCount E ell d b c U m = 0 := by
  have hBound := (integerGraphAgeCanonical_interval_eq_iff_critical_slack
    E ell d b m c hAge).1 hEq U
  omega

/-- A support consuming more raw slack than it has supplies a specific
finite witness that canonical neutrality is impossible. -/
theorem integerGraphAgeCanonical_interval_ne_of_excess_critical_slack
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (c : Nat → Fin d → Bool)
    (hAge : IsIntegerGraphAge d ell
      (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)))
    (U : IntegerGraphSupport d ell)
    (hOver : finiteOldColumnRawBound E ell d (Finset.range b) c U <
      originalCriticalCount E ell d b c U m +
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c) U) :
    integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) ≠
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c) := by
  intro hEq
  have hBudget := (integerGraphAgeCanonical_interval_eq_iff_critical_slack
    E ell d b m c hAge).1 hEq U
  omega

#print axioms Kk.integerGraphAgeCanonical_interval_eq_iff_critical_slack
#print axioms Kk.integerGraphAgeCanonical_every_intermediate_eq_of_critical_slack
#print axioms Kk.originalCriticalCount_zero_of_canonical_interval_eq_tight
#print axioms Kk.integerGraphAgeCanonical_interval_ne_of_excess_critical_slack

end Kk
