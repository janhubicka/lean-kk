import Kk.DiaryCoverColumn
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track F: exact controlled-coding column over arbitrary raw graph-age data

After the coded branch has been deleted, a controlled-coding column
places a new common symbol 1 on precisely a set X of surviving sorts.
The raw bound is capped at ell-2 on every nonempty admissible U ⊆ X.

If the *actual canonical* restricted age F already satisfies these caps,
then applying the column to the potentially NONCANONICAL original raw
bound B leaves the normalized age and all feasible clique vectors unchanged.
This theorem does not construct the deletion/restriction bridge, the
word-level passing edge relation, the diary inverse, or an infinite
Ramsey lower bound.
-/

namespace Kk

/-- Add a uniform raw clique-capacity constraint on every nonempty
admissible support contained in X. The set X itself need not be an
admissible support and may contain more than ell-1 coordinates. -/
def trackFCodingRaw
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat) :
    IntegerGraphSupport d ell → Nat :=
  fun U => if U.1 ⊆ X then min (B U) n else B U

/-- A coding column never weakens the old raw graph-age bounds. -/
theorem trackFCodingRaw_le_original
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat) :
    AgeLe (trackFCodingRaw d ell B X n) B := by
  classical
  intro U
  by_cases h : U.1 ⊆ X
  · simp [trackFCodingRaw, h]
  · simp [trackFCodingRaw, h]

/-- The precise conditional age-preservation step of controlled coding:
a permitted passing-one support X whose true *canonical* age already
respects the cap n cannot create an additional forbidden clique.

In particular, this covers n=ell-2 as in the K_ell coding rule.
The original RAW B need not itself be an age, and X may exceed ell-1
sorts; the hypothesis quantifies over all admissible subsets of X. -/
theorem trackFCodingColumn_canonical_eq
    (d ell : Nat)
    (B F : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hCanonical : integerGraphAgeCanonical d ell B = F)
    (hSafe : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ X → F U ≤ n) :
    integerGraphAgeCanonical d ell
      (trackFCodingRaw d ell B X n) = F := by
  classical
  let B' := trackFCodingRaw d ell B X n
  have hFB : AgeLe F B := by
    intro U
    rw [← hCanonical]
    exact integerGraphAgeCanonical_le_raw d ell B U
  have hFB' : AgeLe F B' := by
    intro U
    by_cases h : U.1 ⊆ X
    · simpa [B', trackFCodingRaw, h] using
        (le_min (hFB U) (hSafe U h))
    · simpa [B', trackFCodingRaw, h] using hFB U
  have hB'B : AgeLe B' B :=
    trackFCodingRaw_le_original d ell B X n
  have hNewAge :
      IsIntegerGraphAge d ell (integerGraphAgeCanonical d ell B') :=
    integerGraphAgeCanonical_is_age d ell B' F hAge hFB'
  have hFNew : AgeLe F (integerGraphAgeCanonical d ell B') :=
    integerGraphAgeCanonical_greatest d ell B' F hAge hFB'
  have hNewF : AgeLe (integerGraphAgeCanonical d ell B') F := by
    have hNewB : AgeLe (integerGraphAgeCanonical d ell B') B := by
      intro U
      exact (integerGraphAgeCanonical_le_raw d ell B' U).trans
        (hB'B U)
    have hGreatest : AgeLe (integerGraphAgeCanonical d ell B')
        (integerGraphAgeCanonical d ell B) :=
      integerGraphAgeCanonical_greatest d ell B
        (integerGraphAgeCanonical d ell B') hNewAge hNewB
    simpa only [hCanonical] using hGreatest
  funext U
  exact Nat.le_antisymm (hNewF U) (hFNew U)

/-- The controlled-coding raw column preserves every single normalized
labelled clique multiplicity vector, not just the maximum bound record. -/
theorem trackFCodingColumn_feasible_iff
    (d ell : Nat)
    (B F : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat)
    (hAge : IsIntegerGraphAge d ell F)
    (hCanonical : integerGraphAgeCanonical d ell B = F)
    (hSafe : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ X → F U ≤ n)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (trackFCodingRaw d ell B X n) w ↔
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
  calc
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell
            (trackFCodingRaw d ell B X n)) w :=
        (integerGraphAgeCanonical_preserves_clique_vectors d ell _ w).symm
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) F w := by
        rw [trackFCodingColumn_canonical_eq d ell B F X n
          hAge hCanonical hSafe]
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
        simpa only [hCanonical] using
          (integerGraphAgeCanonical_preserves_clique_vectors d ell B w)

end Kk
