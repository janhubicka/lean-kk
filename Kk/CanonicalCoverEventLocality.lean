import Kk.IntegerAgeCoverSupport
import Mathlib.Tactic

/-!
# Locality of one genuine canonical graph-age cover macro-event

The English proof and hostile mathematical audit were committed FIRST in
`docs/canonical_cover_event_locality_english_audit.md`, before this file.

Given an ACTUAL cover lower ⋖ upper of normalized finite integer-witness
K_ell graph ages, with the canonical r-vertex clique raw bound cutting a
distinguished support T by one, the final stage is the genuine lower age.

Combine this precise final-stage cover theorem with the independently
verified SINGLE-SUPPORT integer-witness locality theorem. A cover therefore
leaves every disjoint support (hence every subfront disjoint from T) fixed;
more generally, it leaves a support S fixed when every nonempty overlap
support U ⊆ S∩T already has upper(U)≤lower(T).

This is a concrete macro-COVER event consequence, not a formalization of
the entire resolved numerical-H original-vertex gadget, and not proof that
all subfront restrictions are covers or equalities. Dependent full I1/I2/
I3/B3 upper type comparisons and the labelled inverse-source orbit remain
unproved.
-/

namespace Kk

/-- At the FINAL canonical cover-clique vertex, the raw bound is
literally the one-support clipping by the genuine lower age value.
The arithmetic length identity is essential to this equality. -/
theorem integerGraphAge_cover_final_raw_eq_single_bound
    (d ell r : Nat)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hEll : ell = lower T + r + 1) :
    rawCliqueBlockBound ell r upper T =
      integerAgeLowerAt d ell upper T (lower T) := by
  classical
  funext U
  by_cases hUT : U = T
  · subst U
    have hBudget : ell - 1 - r = lower T := by omega
    simp [rawCliqueBlockBound, integerAgeLowerAt, hBudget]
  · simp [rawCliqueBlockBound, integerAgeLowerAt, hUT]

/-- An ACTUAL integer-witness graph-age cover lower ⋖ upper with a
distinguished one-step raw clique bound at T has NO effect at S if
every nonempty overlap support U ⊆ T∩S is already bounded by lower(T).

This uses the genuine canonical cover theorem and the integer-witness
locality proof, not a fictitious 'age = raw table' inference. -/
theorem integerGraphAge_cover_event_preserves_support_of_overlap
    (d ell r : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T S : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hOverlap : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → U.1 ⊆ S.1 → upper U ≤ lower T) :
    lower S = upper S := by
  classical
  have hRaw :=
    integerGraphAge_cover_final_raw_eq_single_bound
      d ell r lower upper T hEll
  have hFinal :
      integerGraphAgeCanonical d ell
        (rawCliqueBlockBound ell r upper T) = lower := by
    simpa using
      (integerGraphAge_canonical_cover_block
        d ell r lower upper T hCover hEll hAt r (le_refl r))
  rw [hRaw] at hFinal
  have hLocal :=
    integerGraphAgeCanonical_single_bound_locality
      d ell hell upper hCover.upper_age T S (lower T) hOverlap
  calc
    lower S = integerGraphAgeCanonical d ell
        (integerAgeLowerAt d ell upper T (lower T)) S :=
      (congrFun hFinal S).symm
    _ = upper S := hLocal

/-- A canonical graph-age cover never changes a support disjoint
from its distinguished changed support T. Overlapping supports can
still change through canonicalization; this is deliberately not an
all-subfront theorem. -/
theorem integerGraphAge_cover_event_preserves_disjoint_support
    (d ell r : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T S : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hDisjoint : Disjoint T.1 S.1) :
    lower S = upper S := by
  apply integerGraphAge_cover_event_preserves_support_of_overlap
    d ell r hell lower upper T S hCover hEll hAt
  intro U hUT hUS
  obtain ⟨x, hx⟩ := U.2.1
  exact False.elim
    ((Finset.disjoint_left.mp hDisjoint) (hUT hx) (hUS hx))

/-- A real canonical cover macro-event is COMPLETELY INVISIBLE
on a selected subfront E disjoint from its changed support T:
every nonempty eligible selected sort subset S⊆E has the same
integer-witness graph age on both sides of the event. -/
theorem integerGraphAge_cover_event_preserves_disjoint_subfront
    (d ell r : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (E : Finset (Fin d))
    (hDisjoint : Disjoint E T.1) :
    ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S = upper S := by
  intro S hSub
  have hTS : Disjoint T.1 S.1 := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxS
    have hxE : x ∈ E := hSub hxS
    exact (Finset.disjoint_left.mp hDisjoint) hxE hxT
  exact integerGraphAge_cover_event_preserves_disjoint_support
    d ell r hell lower upper T S hCover hEll hAt hTS


/-- A canonical cover with an inclusion-minimal changed support T
cannot change ANY support S which does NOT contain T, even if
S overlaps T. The minimum-support assumption is displayed explicitly:
the previous uniqueness theorem does not silently supply existence
or identify the cover's chosen T as that minimum. -/
theorem integerGraphAge_cover_event_preserves_without_full_support
    (d ell r : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T S : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hMinimal : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U)
    (hNot : ¬ T.1 ⊆ S.1) :
    lower S = upper S := by
  apply integerGraphAge_cover_event_preserves_support_of_overlap
    d ell r hell lower upper T S hCover hEll hAt
  intro U hUT hUS
  have hProper : U.1 ≠ T.1 := by
    intro hEqual
    apply hNot
    simpa only [hEqual] using hUS
  have hSame : lower U = upper U :=
    hMinimal U hUT hProper
  calc
    upper U = lower U := hSame.symm
    _ ≤ lower T :=
      integerGraphAge_monotone d ell lower hCover.lower_age U T hUT

/-- The ENTIRE selected graph-age restriction on any subfront E
omitting at least one sort of an inclusion-minimal changed
cover support T is unchanged. This is stronger than disjointness:
E may contain arbitrarily many but not ALL sorts of T. -/
theorem integerGraphAge_cover_event_preserves_subfront_omitting_support
    (d ell r : Nat) (hell : 0 < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hEll : ell = lower T + r + 1)
    (hAt : upper T = lower T + 1)
    (hMinimal : ∀ U : IntegerGraphSupport d ell,
      U.1 ⊆ T.1 → U.1 ≠ T.1 → lower U = upper U)
    (E : Finset (Fin d))
    (hNot : ¬ T.1 ⊆ E) :
    ∀ S : IntegerGraphSupport d ell,
      S.1 ⊆ E → lower S = upper S := by
  intro S hSub
  apply integerGraphAge_cover_event_preserves_without_full_support
    d ell r hell lower upper T S hCover hEll hAt hMinimal
  intro hTS
  exact hNot (hTS.trans hSub)

end Kk
