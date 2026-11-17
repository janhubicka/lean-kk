import Kk.TrackFActualCodingFibre
import Mathlib.Tactic

/-!
# Track F: source distinguishing old bits force different target fibres

English proof and hostile audit committed before Lean:
docs/track_f_distinct_target_prefixes_english_audit.md

Two genuine finite source Henson one-types differing at a common OLD
source coordinate cannot have actual coding descendants whose
images under an INDUCED graph map both realize the SAME target
prefix type after the image of that separating coordinate.

This uses actual original coding-node columns and the exact
sourceCodingFibre predicate, not hypothetical diary age equality,
a Ramsey theorem or source/target enumeration monotonicity.

It verifies the finite target DISTINCTNESS implication of the
pending multi-sort profile synchronization lemma. It does not
prove the existence of simultaneous rank-large target fibres
or equality of their entire mixed graph-age profiles.
-/

namespace Kk.HensonOneType

variable {ell : Nat}

/-- A genuine source old bit distinction survives to ACTUAL
source coding originals and then, under inducedness, to their
target image old bits. Hence two coding descendants of distinct
source old-bit types cannot both lie in the SAME target type
fibre if that target prefix includes the image of the
distinguishing source old coordinate.

The embedding need NOT preserve natural-number order. -/
theorem different_source_bits_prevent_same_target_fibre
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u v : HensonOneType ell Esrc)
    (a : Nat) (haU : a < u.level) (haV : a < v.level)
    (hDiff : ¬ (a ∈ u.neighbours ↔ a ∈ v.neighbours))
    (x y : HensonOneType ell Esrc)
    (hux : u ≤ x) (hvy : v ≤ y)
    (t : HensonOneType ell Etgt)
    (haTarget : e a < t.level)
    (hxFibre : x ∈ sourceCodingFibre (E := Esrc) Etgt e t)
    (hyFibre : y ∈ sourceCodingFibre (E := Esrc) Etgt e t) :
    False := by
  have haXLt : a < x.level := lt_of_lt_of_le haU hux.1
  have haYLt : a < y.level := lt_of_lt_of_le haV hvy.1
  have hxaNe : a ≠ x.level := by omega
  have hyaNe : a ≠ y.level := by omega
  have hUXBits : decide (a ∈ x.neighbours) =
      decide (a ∈ u.neighbours) := by
    by_cases hau : a ∈ u.neighbours
    · have hax : a ∈ x.neighbours :=
        (hux.2 a haU).mp hau
      simp [hau,hax]
    · have hax : a ∉ x.neighbours := by
        intro hx
        exact hau ((hux.2 a haU).mpr hx)
      simp [hau,hax]
  have hVYBits : decide (a ∈ y.neighbours) =
      decide (a ∈ v.neighbours) := by
    by_cases hav : a ∈ v.neighbours
    · have hay : a ∈ y.neighbours :=
        (hvy.2 a haV).mp hav
      simp [hav,hay]
    · have hay : a ∉ y.neighbours := by
        intro hy
        exact hav ((hvy.2 a haV).mpr hy)
      simp [hav,hay]
  have hXSource : Esrc a x.level =
      decide (a ∈ u.neighbours) :=
    ((hxFibre.1 a haXLt).1).trans hUXBits
  have hYSource : Esrc a y.level =
      decide (a ∈ v.neighbours) :=
    ((hyFibre.1 a haYLt).1).trans hVYBits
  have hXTarget : Etgt (e a) (e x.level) =
      decide (e a ∈ t.neighbours) :=
    (hxFibre.2.2 (e a) haTarget).1
  have hYTarget : Etgt (e a) (e y.level) =
      decide (e a ∈ t.neighbours) :=
    (hyFibre.2.2 (e a) haTarget).1
  have hOldDecideEq :
      decide (a ∈ u.neighbours) =
        decide (a ∈ v.neighbours) := by
    calc
      decide (a ∈ u.neighbours) =
        Esrc a x.level := hXSource.symm
      _ = Etgt (e a) (e x.level) := hInduced a x.level hxaNe
      _ = decide (e a ∈ t.neighbours) := hXTarget
      _ = Etgt (e a) (e y.level) := hYTarget.symm
      _ = Esrc a y.level := (hInduced a y.level hyaNe).symm
      _ = decide (a ∈ v.neighbours) := hYSource
  apply hDiff
  constructor
  · intro hau
    have hTrue : decide (a ∈ u.neighbours) = true := by
      simp [hau]
    rw [hOldDecideEq] at hTrue
    simpa only [decide_eq_true_eq] using hTrue
  · intro hav
    have hTrue : decide (a ∈ v.neighbours) = true := by
      simp [hav]
    rw [← hOldDecideEq] at hTrue
    simpa only [decide_eq_true_eq] using hTrue

/-- If two ACTUAL source coding descendants come from different
source old-bit types, their corresponding target prefixes at
the SAME later target level H CANNOT BE IDENTICAL once H includes
the image of a separating source coordinate.

The target types are genuine Henson finite types. We do not
assume target Henson avoidance in this BIT-DISTINCTNESS lemma:
only the exact target coding-fibre column equalities matter. -/
theorem target_prefix_types_distinct_of_source_old_bit
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (u v : HensonOneType ell Esrc)
    (a : Nat) (haU : a < u.level) (haV : a < v.level)
    (hDiff : ¬ (a ∈ u.neighbours ↔ a ∈ v.neighbours))
    (x y : HensonOneType ell Esrc)
    (hux : u ≤ x) (hvy : v ≤ y)
    (tX tY : HensonOneType ell Etgt)
    (haTarget : e a < tX.level)
    (hxFibre : x ∈ sourceCodingFibre (E := Esrc) Etgt e tX)
    (hyFibre : y ∈ sourceCodingFibre (E := Esrc) Etgt e tY) :
    tX ≠ tY := by
  intro hEq
  subst tY
  exact different_source_bits_prevent_same_target_fibre
    Esrc Etgt e hInduced u v a haU haV hDiff
    x y hux hvy tX haTarget hxFibre hyFibre

end Kk.HensonOneType
