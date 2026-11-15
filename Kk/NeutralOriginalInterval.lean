import Kk.FullOriginalInsertionAge
import Mathlib.Tactic

/-!
# Track B: finite chains of genuine age-neutral original insertions

English-first mathematical proof and adversarial check:
docs/track_b_neutral_interval_sort_image_english_audit.md

This is an exact FINITE induction over actual successive original-prefix
indices. At every original step it requires BOTH a true complete
old-neighbourhood K_ell safety certificate and an all-nonempty-support
mutual-clique no-growth certificate for the SAME unchanged typed
future column. It then proves K_ell-freeness and equality of complete
raw and integer-canonical old-column ages through the whole interval.

It does not construct the certificates, preserve changing future-sort
dimensions through split/coding events, compare auxiliary Kpt L+ sources,
or produce a global bounded resolved diary.
-/

namespace Kk

/-- A finite interval of actual original insertions is safe and exactly
neutral for the complete full-sort raw and canonical ages whenever
EVERY intervening original step carries its true complete-neighbourhood
negative checker and ALL-SUPPORT mutual old-neighbour budget. -/
theorem actual_original_neutral_interval_preserves_free_raw_canonical
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false)
    (c : Nat → Fin d → Bool)
    (hOld : ¬ HasCliqueBelow E b ell)
    (hChecks : ∀ i, b ≤ i → i < b+m →
      finiteNeighbourCliqueCheck E i (ell-1)
        (fun x => E x i) = false)
    (hBudgets : ∀ i, b ≤ i → i < b+m →
      ∀ U : IntegerGraphSupport d ell,
        (∀ t ∈ U.1, c i t = true) →
        1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool (Finset.range i) c U.1) i) ≤
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range i) c U.1)) :
    (¬ HasCliqueBelow E (b+m) ell) ∧
    (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c =
      finiteOldColumnRawBound E ell d (Finset.range b) c) ∧
    (integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) =
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range b) c)) := by
  have hAll : ∀ n : Nat,
      (∀ i, b ≤ i → i < b+n →
        finiteNeighbourCliqueCheck E i (ell-1)
          (fun x => E x i) = false) →
      (∀ i, b ≤ i → i < b+n →
        ∀ U : IntegerGraphSupport d ell,
          (∀ t ∈ U.1, c i t = true) →
          1 + finiteDirectedCliqueCapacity E
            (mutualLinkedNeighbours E
              (oldSupportCommonNeighbourPool (Finset.range i) c U.1) i) ≤
          finiteDirectedCliqueCapacity E
            (oldSupportCommonNeighbourPool (Finset.range i) c U.1)) →
      (¬ HasCliqueBelow E (b+n) ell) ∧
      (finiteOldColumnRawBound E ell d (Finset.range (b+n)) c =
        finiteOldColumnRawBound E ell d (Finset.range b) c) ∧
      (integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range (b+n)) c) =
        integerGraphAgeCanonical d ell
          (finiteOldColumnRawBound E ell d (Finset.range b) c)) := by
    intro n
    induction n with
    | zero =>
      intro _ _
      simp only [Nat.add_zero]
      exact ⟨hOld, rfl, rfl⟩
    | succ n ih =>
      intro hChecksN hBudgetsN
      obtain ⟨hPrevFree, hPrevRaw, hPrevCanonical⟩ :=
        ih (fun i hi hb => hChecksN i hi (by omega))
           (fun i hi hb => hBudgetsN i hi (by omega))
      obtain ⟨hNewFree, hNewRaw, hNewCanonical⟩ :=
        actual_original_stage_preserves_free_and_all_support_age
          E ell d (b+n) hEll hSym hLoops c hPrevFree
          (hChecksN (b+n) (by omega) (by omega))
          (hBudgetsN (b+n) (by omega) (by omega))
      rw [Nat.add_succ]
      exact ⟨hNewFree, hNewRaw.trans hPrevRaw,
        hNewCanonical.trans hPrevCanonical⟩
  exact hAll m hChecks hBudgets

/-- An initial pointwise full canonical reference-age invariant is
preserved through any finite block of certified NEUTRAL insertions.
This supplies the reusable hPrior for a *later* genuine cover stage,
but does not manufacture a cover drop or an infinite diary. -/
theorem actual_original_neutral_interval_preserves_prior_age
    (E : Nat → Nat → Bool) (ell d b m : Nat)
    (hEll : 0 < ell)
    (hSym : ∀ x y, E x y = E y x)
    (hLoops : ∀ x, E x x = false)
    (c : Nat → Fin d → Bool)
    (upper : IntegerGraphSupport d ell → Nat)
    (hOld : ¬ HasCliqueBelow E b ell)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hChecks : ∀ i, b ≤ i → i < b+m →
      finiteNeighbourCliqueCheck E i (ell-1)
        (fun x => E x i) = false)
    (hBudgets : ∀ i, b ≤ i → i < b+m →
      ∀ U : IntegerGraphSupport d ell,
        (∀ t ∈ U.1, c i t = true) →
        1 + finiteDirectedCliqueCapacity E
          (mutualLinkedNeighbours E
            (oldSupportCommonNeighbourPool (Finset.range i) c U.1) i) ≤
        finiteDirectedCliqueCapacity E
          (oldSupportCommonNeighbourPool (Finset.range i) c U.1)) :
    (¬ HasCliqueBelow E (b+m) ell) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range (b+m)) c) = upper := by
  obtain ⟨hFree, _hRaw, hCanonical⟩ :=
    actual_original_neutral_interval_preserves_free_raw_canonical
      E ell d b m hEll hSym hLoops c hOld hChecks hBudgets
  exact ⟨hFree, hCanonical.trans hPrior⟩

#print axioms Kk.actual_original_neutral_interval_preserves_free_raw_canonical
#print axioms Kk.actual_original_neutral_interval_preserves_prior_age

end Kk
