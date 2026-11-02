import Kk.IntegerWitnessCanonical
import Mathlib.Tactic

/-!
# Universal properties of the integer-witness graph-age canonicalizer

The manuscript asserts that a raw clique-capacity bound B and its
canonical graph-age function G_B define exactly the same labelled
K_ell-free clique configurations.

Here a labelled clique is represented by a finite nonnegative
multiplicity vector of total size at most ell-1. The definition of
G_B as the supremum over *all feasible* vectors yields equivalence
of the full inequality systems, with no hypothesis of B already
being an age. Consequently G_F = F for any genuine age F, and
the canonicalizer is idempotent above a genuine age.

The correspondence to unrestricted total-weight vectors is handled
in a separate normalization PR. None of these statements constructs
a numerical-H auxiliary clique block or a labelled diary orbit.
-/

namespace Kk

/-- Exactly the same bounded-total labelled clique multiplicities
satisfy the raw bound B and its canonicalization G_B. -/
theorem integerGraphAgeCanonical_preserves_clique_vectors
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell))
      (integerGraphAgeCanonical d ell B) w ↔
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) B w := by
  constructor
  · intro h T
    exact (h T).trans (integerGraphAgeCanonical_le_raw d ell B T)
  · intro h T
    exact witnessValue_le_canonical
      (integerCliqueOnSupport (d := d) (ell := ell))
      B w h T

/-- Every genuine graph age is a fixed point of canonicalization. -/
theorem integerGraphAgeCanonical_fixed_of_age
    (d ell : Nat)
    (F : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell F) :
    integerGraphAgeCanonical d ell F = F := by
  funext T
  exact Nat.le_antisymm
    (integerGraphAgeCanonical_le_raw d ell F T)
    (integerGraphAgeCanonical_greatest d ell F F hAge
      (fun _ => le_refl _) T)

/-- Whenever a raw bound admits a genuine age below it, its
canonicalization is already a fixed point: applying it again
changes nothing. -/
theorem integerGraphAgeCanonical_idempotent_above_age
    (d ell : Nat)
    (B H : IntegerGraphSupport d ell → Nat)
    (hAge : IsIntegerGraphAge d ell H)
    (hHB : AgeLe H B) :
    integerGraphAgeCanonical d ell
      (integerGraphAgeCanonical d ell B) =
    integerGraphAgeCanonical d ell B := by
  exact integerGraphAgeCanonical_fixed_of_age d ell
    (integerGraphAgeCanonical d ell B)
    (integerGraphAgeCanonical_is_age d ell B H hAge hHB)

end Kk
