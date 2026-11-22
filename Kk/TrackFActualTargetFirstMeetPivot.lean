import Kk.TrackFTrueTargetSplitPivotLex
import Kk.TrackFPairwiseTargetSeparation
import Mathlib.Tactic

/-!
# Track F: TRUE first target meeting pivot of two distinct daughters

Adversarially audited English proof committed FIRST:
docs/track_f_actual_target_first_meet_pivot_english_audit_20261122.md
(20 explicit mathematical/scope checks).

Two genuine target daughters at a common finite chronological level
H which extend the SAME genuine target parent but are DISTINCT
must have a LEAST genuine target coordinate L where their old
positive-neighbour bits differ. This L is at least the old parent's
level and strictly less than H; ALL earlier target bits agree.
The 0/1 orientation at L determines the TRUE target lex order.

This corrects the tempting but UNSOUND assumption that a chosen
SOURCE splitting pivot q maps to the exact first TARGET differing
coordinate e(q) under a nonmonotone induced embedding. The target
meeting pivot is derived from the genuine synchronized target
types themselves, not supplied as a fictitious hypothesis.

The independently verified pivot/no-interleaving lemma (#505)
then controls the relative order of every old unrelated branch.
No rank drop, numerical split age, full dependent diary or BRD
lower bound follows solely from this finite lex-geometry fact.
-/

namespace Kk.HensonOneType

/-- If two DISTINCT genuine target finite types a,b extend the SAME
old parent and have the SAME chronological level H, there is an
ACTUAL LEAST TARGET old-bit first-difference coordinate L.

It satisfies parent.level ≤ L < H, all earlier bits agree, and
exactly one of the two daughter types has positive old bit at L.

The source splitting pivot q and the target meeting pivot L are
NOT assumed equal or related by an order-preserving index map. -/
theorem exists_least_target_meet_pivot_of_distinct_daughters
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent a b : HensonOneType ell E)
    (H : Nat)
    (haLevel : a.level = H)
    (hbLevel : b.level = H)
    (hParentA : parent ≤ a)
    (hParentB : parent ≤ b)
    (hDifferent : a ≠ b) :
    ∃ L : Nat,
      parent.level ≤ L ∧
      L < H ∧
      (∀ x : Nat, x < L →
        (x ∈ a.neighbours ↔ x ∈ b.neighbours)) ∧
      ((L ∉ a.neighbours ∧ L ∈ b.neighbours) ∨
       (L ∈ a.neighbours ∧ L ∉ b.neighbours)) := by
  classical
  have hSetDifferent : a.neighbours ≠ b.neighbours := by
    intro hSame
    exact hDifferent
      (eq_of_level_neighbours a b
        (haLevel.trans hbLevel.symm) hSame)
  have hExists :
      ∃ x : Nat, x < H ∧
        ¬ (x ∈ a.neighbours ↔ x ∈ b.neighbours) := by
    by_contra hNo
    have hSameBits : ∀ x : Nat, x < H →
        (x ∈ a.neighbours ↔ x ∈ b.neighbours) := by
      intro x hx
      by_contra hBad
      exact hNo ⟨x, hx, hBad⟩
    apply hSetDifferent
    ext x
    by_cases hx : x < H
    · exact hSameBits x hx
    · have hAnot : x ∉ a.neighbours := by
        intro hxa
        have hBelow := a.below x hxa
        rw [haLevel] at hBelow
        exact hx hBelow
      have hBnot : x ∉ b.neighbours := by
        intro hxb
        have hBelow := b.below x hxb
        rw [hbLevel] at hBelow
        exact hx hBelow
      exact ⟨(fun hxa => False.elim (hAnot hxa)),
        (fun hxb => False.elim (hBnot hxb))⟩
  let L : Nat := Nat.find hExists
  have hL : L < H ∧
      ¬ (L ∈ a.neighbours ↔ L ∈ b.neighbours) :=
    Nat.find_spec hExists
  have hFirst :
      ∀ x : Nat, x < L →
        (x ∈ a.neighbours ↔ x ∈ b.neighbours) := by
    intro x hx
    have hxH : x < H := lt_trans hx hL.1
    by_contra hBad
    exact (Nat.find_min' hExists hx) ⟨hxH, hBad⟩
  have hParentBefore : parent.level ≤ L := by
    by_contra hNot
    have hOld : L < parent.level :=
      Nat.lt_of_not_ge hNot
    exact hL.2
      (((hParentA.2 L hOld).symm).trans (hParentB.2 L hOld))
  refine ⟨L, hParentBefore, hL.1, hFirst, ?_⟩
  by_cases hA : L ∈ a.neighbours
  · have hB : L ∉ b.neighbours := by
      intro hb
      exact hL.2 ⟨(fun _ => hb), (fun _ => hA)⟩
    exact Or.inr ⟨hA, hB⟩
  · have hB : L ∈ b.neighbours := by
      by_contra hb
      exact hL.2 ⟨
        (fun ha => False.elim (hA ha)),
        (fun hb' => False.elim (hb hb'))⟩
    exact Or.inl ⟨hA, hB⟩

/-- The actual TARGET first-difference of two distinct genuine
same-level daughters extending a common parent exists, and
strictly orders them in EXACTLY one of the two binary lex
orientations. No source daughter name or image-pivot assumption. -/
theorem target_split_daughters_lex_comparable
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent a b : HensonOneType ell E)
    (H : Nat)
    (haLevel : a.level = H)
    (hbLevel : b.level = H)
    (hParentA : parent ≤ a)
    (hParentB : parent ≤ b)
    (hDifferent : a ≠ b) :
    lexBefore a b ∨ lexBefore b a := by
  obtain ⟨L, _hParent, hL, hFirst, hBit⟩ :=
    exists_least_target_meet_pivot_of_distinct_daughters
      parent a b H haLevel hbLevel
      hParentA hParentB hDifferent
  rcases hBit with ⟨haZero, hbOne⟩ | ⟨haOne, hbZero⟩
  · left
    refine ⟨L, ?_, ?_, hFirst, haZero, hbOne⟩
    · simpa only [haLevel] using hL
    · simpa only [hbLevel] using hL
  · right
    refine ⟨L, ?_, ?_, ?_, hbZero, haOne⟩
    · simpa only [hbLevel] using hL
    · simpa only [haLevel] using hL
    · intro x hx
      exact (hFirst x hx).symm

/-- The TRUE meeting pivot and strict binary target daughter
orientation can be extracted from two distinct synchronized
target daughters. Every OTHER old target branch already on one
side of the common parent remains on the SAME side of BOTH true
refined daughters, so no previous branch can interleave.

The lex alternatives are intentionally explicit: a possibly
nonmonotone source-to-target embedding does not determine which
source-labelled daughter becomes target-left. -/
theorem target_split_meet_and_no_old_branch_interleaving
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent a b otherOld otherNew : HensonOneType ell E)
    (H : Nat)
    (haLevel : a.level = H)
    (hbLevel : b.level = H)
    (hParentA : parent ≤ a)
    (hParentB : parent ≤ b)
    (hDifferent : a ≠ b)
    (hOtherExt : otherOld ≤ otherNew)
    (hOldPosition :
      lexBefore otherOld parent ∨ lexBefore parent otherOld) :
    ∃ L : Nat,
      parent.level ≤ L ∧ L < H ∧
      (∀ x : Nat, x < L →
        (x ∈ a.neighbours ↔ x ∈ b.neighbours)) ∧
      (lexBefore a b ∨ lexBefore b a) ∧
      ((lexBefore otherNew a ∧ lexBefore otherNew b) ∨
       (lexBefore a otherNew ∧ lexBefore b otherNew)) := by
  obtain ⟨L, hAfter, hL, hFirst, _hBits⟩ :=
    exists_least_target_meet_pivot_of_distinct_daughters
      parent a b H haLevel hbLevel
      hParentA hParentB hDifferent
  have hLex : lexBefore a b ∨ lexBefore b a :=
    target_split_daughters_lex_comparable
      parent a b H haLevel hbLevel
      hParentA hParentB hDifferent
  have hOther :
      (lexBefore otherNew a ∧ lexBefore otherNew b) ∨
      (lexBefore a otherNew ∧ lexBefore b otherNew) := by
    rcases hOldPosition with hBefore | hAfter
    · exact Or.inl
        (oldBranch_left_of_both_splitDaughters
          otherOld otherNew parent a b
          hBefore hOtherExt hParentA hParentB)
    · exact Or.inr
        (oldBranch_right_of_both_splitDaughters
          parent a b otherOld otherNew
          hAfter hOtherExt hParentA hParentB)
  exact ⟨L, hAfter, hL, hFirst, hLex, hOther⟩

end Kk.HensonOneType
