import Kk.TrackFFullActualZeroCodeAgeStep
import Kk.TrackFTargetLexOrderPersistence
import Mathlib.Tactic

/-!
# Track F: exact target lex order survives ACTUAL independent coding

The English mathematical proof and 17 adversarial checks were written
FIRST in:
docs/track_f_zero_code_chronology_lex_english_audit_20261122.md

Merged #500 physically constructs an actual code original, a genuine
full pre-code front, true post-code surviving prefixes and a common
later target front with COMPLETE canonical K4 ages. The strengthened
public statement of #500 now also exposes the literal pre→post
chronological type extensions of every REAL surviving coordinate
and equality of their genuine old positive-neighbour sets.

This module applies the verified target binary lex first-difference
invariant (#498): if the old TARGET checkpoint sorts are genuinely
lex-sorted, then full pre-code types, immediately post-code REAL
survivors, and later synchronized survivors remain in that exact
TARGET lex order through refinement and the monotone code-deletion
map Fin.succAboveEmb. Source-to-target e may arbitrarily scramble
original index order and source lex order.

The statement does not determine the lex order of newborn split
daughter branches, full Kpt E/parameter history, diary orbit or BRD.
-/

namespace Kk

/-- GENUINE target lex-sortedness of one old finite K4 front persists
through three true physical fronts of an independent code event:
(1) all full pre-code target types, including the terminating code;
(2) the immediate post-code target prefixes on exactly REAL survivors;
(3) the later synchronized surviving target types.

The pre→post chronological refinements are genuine Henson type
extensions, NOT a consequence of mere numeric age equality. The
exact order-preserving deletion f=Fin.succAboveEmb j refers to TARGET
indices, not the possibly different source lex enumeration.

In particular the selected target coordinate order is inherited
without any fresh reindexing when a code type is deleted. The new
daughter order of a SPLIT remains a separate condition. -/
theorem trackFActualZeroCode_target_lex_sorted_invariant
    (d ell : Nat) (E : Nat → Nat → Bool)
    (j : Fin (d + 1))
    (old pre : Fin (d + 1) → HensonOneType ell E)
    (post later : Fin d → HensonOneType ell E)
    (hOldSorted :
      HensonOneType.IsTargetLexSorted (d + 1) ell E old)
    (hOldPre : ∀ i, old i ≤ pre i)
    (hPrePost :
      ∀ i : Fin d, pre (Fin.succAboveEmb j i) ≤ post i)
    (hOldLater :
      ∀ i : Fin d, old (Fin.succAboveEmb j i) ≤ later i) :
    HensonOneType.IsTargetLexSorted (d + 1) ell E pre ∧
    HensonOneType.IsTargetLexSorted d ell E post ∧
    HensonOneType.IsTargetLexSorted d ell E later := by
  have hOldPost :
      ∀ i : Fin d, old (Fin.succAboveEmb j i) ≤ post i := by
    intro i
    exact le_trans (hOldPre (Fin.succAboveEmb j i)) (hPrePost i)
  exact ⟨
    HensonOneType.targetLexSorted_of_extensions
      (d + 1) ell E old pre hOldSorted hOldPre,
    HensonOneType.targetLexSorted_survivors_of_extensions
      d ell E j old post hOldSorted hOldPost,
    HensonOneType.targetLexSorted_survivors_of_extensions
      d ell E j old later hOldSorted hOldLater⟩

end Kk
