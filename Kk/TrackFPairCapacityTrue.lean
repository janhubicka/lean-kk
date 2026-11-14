import Kk.TrackFPairCapacity
import Kk.TrackFSingletonCapacity
import Mathlib.Tactic

/-!
# Track F: real two-sort capacity formula using canonical singleton ages

Combines the actual normalized integer-witness two-sort supremum
with the raw-singleton fixed point under SUPPORT-MONOTONE raw bounds.
The resulting expression is the numerical formula needed for the
word E versus abstract passing-one set, but the branch-spectrum
initial-segment invariant is a separate unproved diary obligation.
-/

namespace Kk

/-- For true support-monotone bounded raw capacities, the canonical
pair capacity is the minimum of the raw pair cap and the SUM OF
THE TWO GENUINE CANONICAL SINGLETON AGES.

This theorem is about actual K_ell normalized integer clique
witnesses, not an abstract surrogate or a claimed diary inverse. -/
theorem trackFPair_canonical_true_singletons
    (ell : Nat) (hell : 3 ≤ ell)
    (B : IntegerGraphSupport 2 ell → Nat)
    (hMono : TrackFRawSupportMonotone 2 ell B)
    (hBound : ∀ U : IntegerGraphSupport 2 ell, B U ≤ ell - 1) :
    integerGraphAgeCanonical 2 ell B (trackFPairBoth ell hell) =
      min (B (trackFPairBoth ell hell))
        (integerGraphAgeCanonical 2 ell B (trackFPairFirst ell hell) +
         integerGraphAgeCanonical 2 ell B (trackFPairSecond ell hell)) := by
  let h2 : 2 ≤ ell := by omega
  have hFirst :
      trackFSingletonSupport 2 ell (0 : Fin 2) h2 =
        trackFPairFirst ell hell := by
    apply Subtype.ext
    rfl
  have hSecond :
      trackFSingletonSupport 2 ell (1 : Fin 2) h2 =
        trackFPairSecond ell hell := by
    apply Subtype.ext
    rfl
  have h0 :
      integerGraphAgeCanonical 2 ell B (trackFPairFirst ell hell) =
        B (trackFPairFirst ell hell) := by
    have hCap : B (trackFSingletonSupport 2 ell (0 : Fin 2) h2) ≤
        ell - 1 := by rw [hFirst]; exact hBound _
    exact hFirst ▸
      (trackFCanonical_singleton_eq_raw
        2 ell h2 B hMono (0 : Fin 2) hCap)
  have h1 :
      integerGraphAgeCanonical 2 ell B (trackFPairSecond ell hell) =
        B (trackFPairSecond ell hell) := by
    have hCap : B (trackFSingletonSupport 2 ell (1 : Fin 2) h2) ≤
        ell - 1 := by rw [hSecond]; exact hBound _
    exact hSecond ▸
      (trackFCanonical_singleton_eq_raw
        2 ell h2 B hMono (1 : Fin 2) hCap)
  rw [trackFPair_canonical_capacity ell hell B (hBound _)]
  rw [h0, h1]

end Kk
