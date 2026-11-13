import Kk.TrackFCodingColumn
import Kk.DiaryCoverColumn
import Kk.IntegerAgeUniversalProperties
import Mathlib.Tactic

/-!
# Track F: a literal raw-word cover column, not just a canonical age cover

The manuscript computes concrete word ages as G_phi where phi is a
generally noncanonical raw common-symbol bound. Previous age-cover
results began from F=G_phi rather than phi itself. This module proves
that adding any common-symbol cap to both phi and F gives identical
feasible normalized clique-vector sets, hence identical canonical
ages. Specializing to a genuine cover F' ⋖ F recovers exactly F'
from the literal raw column on a changed support.

No word-construction, diary inverse, controlled coding edges,
parameter-closed B3 or infinite unavoidability is claimed.
-/

namespace Kk

/-- A common-symbol column bound is equivalent to the original raw
bound plus the uniform cap on every affected nonempty support. -/
theorem trackFCodingRaw_witness_iff
    (d ell : Nat)
    (B : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell))
        (trackFCodingRaw d ell B X n) w ↔
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w ∧
      (∀ U : IntegerGraphSupport d ell,
        U.1 ⊆ X → integerCliqueOnSupport w U ≤ n) := by
  classical
  constructor
  · intro h
    constructor
    · intro U
      exact (h U).trans
        (trackFCodingRaw_le_original d ell B X n U)
    · intro U hU
      have hBound : integerCliqueOnSupport w U ≤ min (B U) n := by
        simpa [trackFCodingRaw, hU] using (h U)
      exact hBound.trans (Nat.min_le_right (B U) n)
  · rintro ⟨hB, hCap⟩ U
    by_cases hU : U.1 ⊆ X
    · simpa [trackFCodingRaw, hU] using
        (le_min (hB U) (hCap U hU))
    · simpa [trackFCodingRaw, hU] using hB U

/-- Two raw bound records with the same feasible normalized clique
vectors have exactly the same canonical graph-age function.
No admissibility or positive-lower-bound assumptions on B,C. -/
theorem trackFCanonical_eq_of_feasible_iff
    (d ell : Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (hSame : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w ↔
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) C w) :
    integerGraphAgeCanonical d ell B = integerGraphAgeCanonical d ell C := by
  classical
  let value := integerCliqueOnSupport (d := d) (ell := ell)
  have hFilter :
      (Finset.univ.filter (WitnessRespects value B) :
        Finset (IntegerCliqueWeights d ell)) =
      Finset.univ.filter (WitnessRespects value C) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSame w
  funext T
  change
    (Finset.univ.filter (WitnessRespects value B)).sup
       (fun w => value w T) =
    (Finset.univ.filter (WitnessRespects value C)).sup
       (fun w => value w T)
  rw [hFilter]

/-- Adding the *same* actual concrete symbol-column cap commutes with
the canonicalization equivalence, even if the old raw bounds have slack. -/
theorem trackFCanonical_add_cap_congr
    (d ell : Nat)
    (B C : IntegerGraphSupport d ell → Nat)
    (X : Finset (Fin d)) (n : Nat)
    (hCanonical :
      integerGraphAgeCanonical d ell B =
      integerGraphAgeCanonical d ell C) :
    integerGraphAgeCanonical d ell
       (trackFCodingRaw d ell B X n) =
    integerGraphAgeCanonical d ell
       (trackFCodingRaw d ell C X n) := by
  have hOld : ∀ w : IntegerCliqueWeights d ell,
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) B w ↔
      WitnessRespects
        (integerCliqueOnSupport (d := d) (ell := ell)) C w := by
    intro w
    calc
      _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell B) w :=
        (integerGraphAgeCanonical_preserves_clique_vectors d ell B w).symm
      _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell C) w := by
        rw [hCanonical]
      _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) C w :=
        integerGraphAgeCanonical_preserves_clique_vectors d ell C w
  apply trackFCanonical_eq_of_feasible_iff d ell
    (trackFCodingRaw d ell B X n)
    (trackFCodingRaw d ell C X n)
  intro w
  rw [trackFCodingRaw_witness_iff d ell B X n w,
      trackFCodingRaw_witness_iff d ell C X n w]
  exact and_congr (hOld w) Iff.rfl

/-- **Exact abstract-to-concrete age-cover bridge:** for *any* raw
word-bound phi with G_phi=upper, imposing the genuine cover's
new capacity lower(T) on all U⊆T canonicalizes to exactly lower.
The earlier age-only result is no longer used as if phi=upper. -/
theorem trackFRawCoverColumn_exact
    (d ell : Nat)
    (B lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCanonical : integerGraphAgeCanonical d ell B = upper)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hChanged : lower T < upper T) :
    integerGraphAgeCanonical d ell
       (trackFCodingRaw d ell B T.1 (lower T)) = lower := by
  calc
    integerGraphAgeCanonical d ell
        (trackFCodingRaw d ell B T.1 (lower T)) =
      integerGraphAgeCanonical d ell
        (trackFCodingRaw d ell upper T.1 (lower T)) :=
      trackFCanonical_add_cap_congr d ell B upper T.1 (lower T)
        (by simpa only [hCanonical] using
          (integerGraphAgeCanonical_fixed_of_age d ell upper
            hCover.upper_age).symm)
    _ = lower := by
      change integerGraphAgeCanonical d ell
        (diaryCoverColumnRaw d ell upper T (lower T)) = lower
      exact diaryCoverColumnCanonical_exact d ell lower upper T
        hCover hChanged

/-- Every normalized clique vector survives the literal raw
age-change word column exactly when it belongs to the intended
lower age; no silent replacement of phi by its canonicalization. -/
theorem trackFRawCoverColumn_feasible_iff_lower
    (d ell : Nat)
    (B lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCanonical : integerGraphAgeCanonical d ell B = upper)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hChanged : lower T < upper T)
    (w : IntegerCliqueWeights d ell) :
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell))
      (trackFCodingRaw d ell B T.1 (lower T)) w ↔
    WitnessRespects
      (integerCliqueOnSupport (d := d) (ell := ell)) lower w := by
  calc
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell))
          (integerGraphAgeCanonical d ell
            (trackFCodingRaw d ell B T.1 (lower T))) w :=
        (integerGraphAgeCanonical_preserves_clique_vectors d ell _ w).symm
    _ ↔ WitnessRespects
          (integerCliqueOnSupport (d := d) (ell := ell)) lower w := by
        rw [trackFRawCoverColumn_exact d ell B lower upper
          T hCanonical hCover hChanged]

end Kk
