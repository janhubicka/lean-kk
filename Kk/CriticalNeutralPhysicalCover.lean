import Kk.CriticalCountSafeAge
import Kk.PhysicalCanonicalCoverStage
import Mathlib.Tactic

/-!
# Track B: one real Henson cover after a certified raw-neutral original interval

The English mathematical proof and hostile checks were committed first:
docs/track_b_critical_neutral_cover_english_audit.md

The previously checked genuine finite physical canonical-cover construction
requires the entire actual canonical old reference age at its starting
original cut to equal the designated upper age pointwise.

The verified critical-original-count telescope supplies that exact hPrior
at b+m from an earlier hPrior at b, PROVIDED the unchanged full typed
future column has zero actual critical-original insertions on EVERY
admissible nonempty support in [b,b+m). No selected-front projection or
global unbounded resolved-copy schedule is assumed.

The result composes a finite neutral original stretch with ONE genuine
canonical cover stage in the fixed Henson original graph and numerical H.
It does not identify full Kpt dependent L+ events or common labelled orbit.
-/

namespace Kk

/-- After an arbitrarily long but FINITE actual original interval with
zero true critical-support counts, the genuine Henson canonical-cover
construction can start at the later original cut b+m and realize the
prescribed age cover using a physically isolated reserved clique Q.

The complete old-prefix hPrior at the later cut is derived, not
postulated. All additional Henson, age-cover and density hypotheses
are exactly those of the previously checked one-stage theorem.

No claim of *generation* of the earlier neutral original columns,
of repeated infinite cover steps, or of matching Kpt auxiliary E
and dependent old/upper L+ microevents is made. -/
theorem henson_leftDense_physical_cover_after_zero_critical_interval
    (d ell b m k r : Nat)
    (hell : 2 ≤ ell) (hd : 0 < d)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (c : Nat → Fin d → Bool)
    (T : IntegerGraphSupport d ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound E ell d (Finset.range b) c) = upper)
    (hZero : ∀ U : IntegerGraphSupport d ell,
      originalCriticalCount E ell d b c U m = 0) :
    ∃ (Q : Finset Nat) (F : Nat),
      Q.card = r ∧
      (∀ q ∈ Q, b+m ≤ q ∧ q < F) ∧
      IsDirectedCliqueOn E Q ∧
      (∀ p, p < b+m → ∀ q ∈ Q,
        E p q = false ∧ E q p = false) ∧
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d (Finset.range F)
          (supportBlockGappedColumn (b+m) Q T.1 c)) = lower ∧
      feasibleIntegerCliqueVectors d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range (b+m) ∪ Q)
          (supportBlockOldColumn Q T.1 c)) =
        feasibleIntegerCliqueVectors d ell lower ∧
      HasUniformPositiveSupportStage E d ell (b+m) F k hd c Q T := by
  have hLaterPrior :
      integerGraphAgeCanonical d ell
        (finiteOldColumnRawBound E ell d
          (Finset.range (b+m)) c) = upper :=
    actual_prior_canonical_age_after_zero_critical_interval
      E ell d b m c upper hPrior hZero
  exact henson_leftDense_exists_physical_finite_canonical_cover_stage
    d ell (b+m) k r hell hd E hAvoid hDense c T
    lower upper hCover hEll hAt hLaterPrior

#print axioms Kk.henson_leftDense_physical_cover_after_zero_critical_interval

end Kk
