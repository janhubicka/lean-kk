import Kk.TrackFTargetLexOrderPersistence
import Mathlib.Tactic

/-!
# Track F: real target pivot daughters form a contiguous lex block

English-first proof and 18 adversarial scope checks committed FIRST:
docs/track_f_true_target_pivot_split_lex_english_audit_20261122.md

Given a GENUINE finite target parent type and two actual Henson type
extensions past its level m whose target pivot bits differ 0/1,
their FIRST binary lexicographic disagreement is exactly m.
All earlier bits are inherited verbatim. This orders the daughters
and keeps them distinct.

Every OTHER old target branch already lex left or right of the
parent stays on the SAME side of BOTH daughters after its own
genuine chronological extension. Thus the daughter pair occupies
a contiguous block among previously selected old branches. No
source→target enumeration-order preservation is assumed.

CRUCIAL SCOPE: This is conditional on an ACTUAL target pivot 0/1 bit
configuration; the lemma does NOT construct the target meeting pivot
from a source fan, the full split age, full Kpt diary, or BRD.
-/

namespace Kk.HensonOneType

/-- Two genuinely distinct target daughters extending the SAME
parent, with bit 0 and bit 1 at its NEXT TARGET original coordinate
m=parent.level, are ordered LEFT<RIGHT by that exact first
different old bit. No source pivot index or rank hypothesis. -/
theorem splitDaughters_lexBefore_of_pivot_bits
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent left right : HensonOneType ell E)
    (hParentLeft : parent ≤ left)
    (hParentRight : parent ≤ right)
    (hLeftAfter : parent.level < left.level)
    (hRightAfter : parent.level < right.level)
    (hLeftZero : parent.level ∉ left.neighbours)
    (hRightOne : parent.level ∈ right.neighbours) :
    lexBefore left right := by
  refine ⟨parent.level, hLeftAfter, hRightAfter, ?_,
    hLeftZero, hRightOne⟩
  intro a ha
  exact ((hParentLeft.2 a ha).symm).trans
    (hParentRight.2 a ha)

/-- An OTHER selected target branch which was strictly lex LEFT
of the old split parent remains strictly left of BOTH genuinely
refined daughters. This preserves its original first difference
without source lex-order or numeric age assumptions. -/
theorem oldBranch_left_of_both_splitDaughters
    {ell : Nat} {E : Nat → Nat → Bool}
    (otherOld otherNew parent left right : HensonOneType ell E)
    (hOldLex : lexBefore otherOld parent)
    (hOtherExt : otherOld ≤ otherNew)
    (hParentLeft : parent ≤ left)
    (hParentRight : parent ≤ right) :
    lexBefore otherNew left ∧ lexBefore otherNew right := by
  exact ⟨
    lexBefore_of_extensions hOtherExt hParentLeft hOldLex,
    lexBefore_of_extensions hOtherExt hParentRight hOldLex⟩

/-- An OTHER selected target branch which was strictly lex RIGHT
of the old split parent remains strictly right of BOTH genuinely
refined daughters. The source embedding need not preserve
chronological or lexicographic index order. -/
theorem oldBranch_right_of_both_splitDaughters
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent left right otherOld otherNew : HensonOneType ell E)
    (hOldLex : lexBefore parent otherOld)
    (hOtherExt : otherOld ≤ otherNew)
    (hParentLeft : parent ≤ left)
    (hParentRight : parent ≤ right) :
    lexBefore left otherNew ∧ lexBefore right otherNew := by
  exact ⟨
    lexBefore_of_extensions hParentLeft hOtherExt hOldLex,
    lexBefore_of_extensions hParentRight hOtherExt hOldLex⟩

/-- Complete LOCAL target split lex-block theorem.

If TRUE target daughters have first different bits 0 and 1 at
their COMMON old parent pivot, they satisfy left<right. Any
OTHER already selected target branch, known to lie strictly to
one side of the old parent, cannot interleave between these two
daughters after chronological refinement.

The result is for ACTUAL Henson finite types and precise TARGET
old bits. It does NOT claim a source marker at q is mapped to the
same target pivot; that is a separate geometric split obligation. -/
theorem splitDaughters_target_lex_block_no_old_interleaving
    {ell : Nat} {E : Nat → Nat → Bool}
    (parent left right otherOld otherNew : HensonOneType ell E)
    (hParentLeft : parent ≤ left)
    (hParentRight : parent ≤ right)
    (hLeftAfter : parent.level < left.level)
    (hRightAfter : parent.level < right.level)
    (hLeftZero : parent.level ∉ left.neighbours)
    (hRightOne : parent.level ∈ right.neighbours)
    (hOtherExt : otherOld ≤ otherNew)
    (hOldPosition :
      lexBefore otherOld parent ∨ lexBefore parent otherOld) :
    lexBefore left right ∧
      ((lexBefore otherNew left ∧ lexBefore otherNew right) ∨
       (lexBefore left otherNew ∧ lexBefore right otherNew)) := by
  refine ⟨splitDaughters_lexBefore_of_pivot_bits
    parent left right hParentLeft hParentRight
    hLeftAfter hRightAfter hLeftZero hRightOne, ?_⟩
  rcases hOldPosition with hBefore | hAfter
  · exact Or.inl (oldBranch_left_of_both_splitDaughters
      otherOld otherNew parent left right
      hBefore hOtherExt hParentLeft hParentRight)
  · exact Or.inr (oldBranch_right_of_both_splitDaughters
      parent left right otherOld otherNew
      hAfter hOtherExt hParentLeft hParentRight)

end Kk.HensonOneType
