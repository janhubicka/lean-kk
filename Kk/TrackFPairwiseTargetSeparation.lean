import Kk.TrackFDistinctTargetPrefixes
import Kk.TrackFRealHensonTypeTree
import Kk.TrackFActualCodingFibre
import Mathlib.Tactic

/-!
# Track F: injective target fronts from true source old-bit separators

English-first proof and 12 adversarial checks:
docs/track_f_pairwise_target_separation_english_audit_20261120.md

Real same-level Henson source types are distinguished by actual OLD
positive/negative bits. Genuine large ACTUAL coding fibres transport
these old bits across any induced graph embedding, regardless of its
chronological order. Once the common target prefix contains images of
all the old source coordinates, target types are pairwise distinct.

No pre-existing global diary lower bound or target profile equality.
-/

namespace Kk.HensonOneType

/-- A genuine finite Henson type has no extra non-Proposition data
beyond its old level and finite old positive-neighbour set.
The safety/boundedness fields are proofs and thus proof-irrelevant. -/
theorem eq_of_level_neighbours
    {ell : Nat} {E : Nat → Nat → Bool}
    (x y : HensonOneType ell E)
    (hLevel : x.level = y.level)
    (hNeigh : x.neighbours = y.neighbours) : x = y := by
  cases x with
  | mk lx nx bx sx =>
    cases y with
    | mk ly ny by sy =>
      change lx = ly at hLevel
      change nx = ny at hNeigh
      subst ly
      subst ny
      rfl

/-- Distinct genuine source one-types sharing the same old prefix
are separated by an actual old positive-neighbour bit. Proof uses
full finite-set extensionality and genuine type field-extensionality. -/
theorem distinct_same_level_source_types_have_old_bit_separator
    (d ell m : Nat) (E : Nat → Nat → Bool)
    (u : Fin d → HensonOneType ell E)
    (hLevel : ∀ i, (u i).level = m)
    (hInj : Function.Injective u) :
    ∀ i j : Fin d, i ≠ j →
      ∃ a : Nat, a < m ∧
        ¬ (a ∈ (u i).neighbours ↔ a ∈ (u j).neighbours) := by
  classical
  intro i j hij
  by_contra hNone
  have hAgree :
      ∀ a : Nat, a < m →
        (a ∈ (u i).neighbours ↔ a ∈ (u j).neighbours) := by
    intro a ha
    by_contra hBad
    exact hNone ⟨a, ha, hBad⟩
  have hNeigh : (u i).neighbours = (u j).neighbours := by
    ext a
    by_cases ha : a < m
    · exact hAgree a ha
    · have hNotI : a ∉ (u i).neighbours := by
        intro hai
        have hLt := (u i).below a hai
        rw [hLevel i] at hLt
        exact ha hLt
      have hNotJ : a ∉ (u j).neighbours := by
        intro haj
        have hLt := (u j).below a haj
        rw [hLevel j] at hLt
        exact ha hLt
      exact iff_of_false hNotI hNotJ
  have hSame : u i = u j :=
    eq_of_level_neighbours (u i) (u j)
      ((hLevel i).trans (hLevel j).symm) hNeigh
  exact hij (hInj hSame)

/-- Arbitrary finite target prefix types are pairwise distinct
whenever their genuine ACTUAL coding fibres have large refined
source cones above OLD roots whose bits have known separators.

The source embedding need not preserve enumeration order;
only the images of the OLD source prefix must be < target H.
No initial target type distinctness is assumed. -/
theorem target_finite_family_injective_of_old_separators
    (d ell m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (t : Fin d → HensonOneType ell Etgt)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hTLevel : ∀ i, (t i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hSourceSeparators : ∀ i j : Fin d, i ≠ j →
      ∃ a : Nat, a < m ∧
        ¬ (a ∈ (uOld i).neighbours ↔ a ∈ (uOld j).neighbours))
    (hImageOld : ∀ a, a < m → e a < H)
    (hLarge : ∀ i,
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e (t i))
        (rank (uNew i)) (uNew i)) :
    Function.Injective t := by
  classical
  intro i j htEq
  by_contra hij
  obtain ⟨a, ha, hDiff⟩ :=
    hSourceSeparators i j hij
  have haI : a < (uOld i).level := by
    simpa only [hOldLevel i] using ha
  have haJ : a < (uOld j).level := by
    simpa only [hOldLevel j] using ha
  have haTarget : e a < (t i).level := by
    simpa only [hTLevel i] using (hImageOld a ha)
  obtain ⟨x, hxAbove, hxFibre⟩ :=
    RankLargeness.large_has_member rank
      (sourceCodingFibre (E := Esrc) Etgt e (t i))
      (rank (uNew i)) (uNew i) rfl (hLarge i)
  obtain ⟨y, hyAbove, hyFibre⟩ :=
    RankLargeness.large_has_member rank
      (sourceCodingFibre (E := Esrc) Etgt e (t j))
      (rank (uNew j)) (uNew j) rfl (hLarge j)
  have hOldX : uOld i ≤ x :=
    le_trans (hRefine i) hxAbove
  have hOldY : uOld j ≤ y :=
    le_trans (hRefine j) hyAbove
  have hDifferent : t i ≠ t j :=
    target_prefix_types_distinct_of_source_old_bit
      Esrc Etgt e hInduced
      (uOld i) (uOld j) a haI haJ hDiff
      x y hOldX hOldY
      (t i) (t j) haTarget hxFibre hyFibre
  exact hDifferent htEq

/-- Distinct genuine OLD roots at common source level automatically
supply all old-bit separators needed to make the actual target tuple
injective. No pairwise target-type distinctness hypothesis is needed. -/
theorem target_finite_family_injective_of_distinct_source_roots
    (d ell m H : Nat)
    (Esrc Etgt : Nat → Nat → Bool)
    (e : Nat → Nat)
    (hInduced : ∀ a b : Nat, a ≠ b →
      Esrc a b = Etgt (e a) (e b))
    (uOld uNew : Fin d → HensonOneType ell Esrc)
    (t : Fin d → HensonOneType ell Etgt)
    (hOldLevel : ∀ i, (uOld i).level = m)
    (hOldInj : Function.Injective uOld)
    (hTLevel : ∀ i, (t i).level = H)
    (hRefine : ∀ i, uOld i ≤ uNew i)
    (hImageOld : ∀ a, a < m → e a < H)
    (hLarge : ∀ i,
      RankLargeness.Large rank
        (sourceCodingFibre (E := Esrc) Etgt e (t i))
        (rank (uNew i)) (uNew i)) :
    Function.Injective t := by
  exact target_finite_family_injective_of_old_separators
    d ell m H Esrc Etgt e hInduced
    uOld uNew t hOldLevel hTLevel hRefine
    (distinct_same_level_source_types_have_old_bit_separator
      d ell m Esrc uOld hOldLevel hOldInj)
    hImageOld hLarge

end Kk.HensonOneType
