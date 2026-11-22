import Kk.TrackFRealHensonTypeTree
import Mathlib.Tactic

/-!
# Track F: actual TARGET binary lex ordering is refinement-invariant

English mathematical proof and 17 adversarial scope checks were
committed FIRST in
docs/track_f_actual_target_lex_persistence_english_audit_20261122.md.

Genuine Henson chronological one-types encode COMPLETE 0/1 old
adjacency words. Lexicographically earlier (alphabet 0<1) means
there is a FIRST genuine old coordinate a where the earlier type
has bit 0, the later one bit 1, and all smaller bits agree.

Genuine complete old-bit refinements preserve that SAME first
difference, no matter what additional positive neighbours or
source originals are chosen later. Finite target fronts therefore
retain their lex order under coordinatewise target refinement,
and REAL survivors retain the true TARGET order under the
strictly monotone Fin.succAboveEmb j deletion of a coded type.

No source chronological-order preservation or abstract diary
unavoidability/BRD claim is assumed.
-/

namespace Kk.HensonOneType

/-- Strict first-difference lex order of the genuine finite 0/1
old-neighbour type words, with 0<1. A first difference must lie in
BOTH type domains. We do not claim two unrelated types are always
comparable when one is a proper prefix of the other. -/
def lexBefore {ell : Nat} {E : Nat → Nat → Bool}
    (u v : HensonOneType ell E) : Prop :=
  ∃ a : Nat,
    a < u.level ∧
    a < v.level ∧
    (∀ b : Nat, b < a →
      (b ∈ u.neighbours ↔ b ∈ v.neighbours)) ∧
    a ∉ u.neighbours ∧
    a ∈ v.neighbours

/-- Lex order cannot reverse after genuine chronological refinement:
the old FIRST 0/1 disagreement is preserved exactly, including
negative old bits. No graph symmetry or edge embedding premise. -/
theorem lexBefore_of_extensions
    {ell : Nat} {E : Nat → Nat → Bool}
    {u v uNew vNew : HensonOneType ell E}
    (hu : u ≤ uNew)
    (hv : v ≤ vNew)
    (hLex : lexBefore u v) :
    lexBefore uNew vNew := by
  obtain ⟨a, haU, haV, hAgree, hZero, hOne⟩ := hLex
  refine ⟨a, lt_of_lt_of_le haU hu.1,
    lt_of_lt_of_le haV hv.1, ?_, ?_, ?_⟩
  · intro b hb
    have hbU : b < u.level := lt_trans hb haU
    have hbV : b < v.level := lt_trans hb haV
    exact ((hu.2 b hbU).symm).trans
      ((hAgree b hb).trans (hv.2 b hbV))
  · intro haNew
    exact hZero ((hu.2 a haU).mpr haNew)
  · exact (hv.2 a haV).mp hOne

/-- A labelled TARGET front is indexed in its actual binary
lex order. This condition concerns the true target old bits, not
the possibly different source-word/embedding lex order. -/
def IsTargetLexSorted
    (d ell : Nat) (E : Nat → Nat → Bool)
    (front : Fin d → HensonOneType ell E) : Prop :=
  ∀ i k : Fin d, i < k → lexBefore (front i) (front k)

/-- Every coordinatewise genuine extension of a lex-sorted target
front remains in the SAME target lex order. In particular no
arbitrary source coordinate or fresh target positive marker can
reverse a previously known first difference. -/
theorem targetLexSorted_of_extensions
    (d ell : Nat) (E : Nat → Nat → Bool)
    (old new : Fin d → HensonOneType ell E)
    (hOldSorted : IsTargetLexSorted d ell E old)
    (hExt : ∀ i, old i ≤ new i) :
    IsTargetLexSorted d ell E new := by
  intro i k hik
  exact lexBefore_of_extensions
    (hExt i) (hExt k) (hOldSorted i k hik)

/-- After ACTUAL independent coding at sort j, the order-preserving
deletion f=Fin.succAboveEmb j, followed by genuine refinements of
the survivors, preserves the TRUE target lexicographic order.

This confirms that the survivor indexing used in the physical
zero-code numeric-age proof is TARGET-order preserving. It does
not decide the order of newly split daughter branches. -/
theorem targetLexSorted_survivors_of_extensions
    (d ell : Nat) (E : Nat → Nat → Bool)
    (j : Fin (d + 1))
    (old : Fin (d + 1) → HensonOneType ell E)
    (later : Fin d → HensonOneType ell E)
    (hOldSorted : IsTargetLexSorted (d + 1) ell E old)
    (hExt : ∀ i, old (Fin.succAboveEmb j i) ≤ later i) :
    IsTargetLexSorted d ell E later := by
  intro i k hik
  have hIK :
      Fin.succAboveEmb j i < Fin.succAboveEmb j k := by
    simpa only [Fin.succAboveEmb_apply] using
      (Fin.strictMono_succAbove j hik)
  exact lexBefore_of_extensions
    (hExt i) (hExt k)
    (hOldSorted (Fin.succAboveEmb j i)
      (Fin.succAboveEmb j k) hIK)

end Kk.HensonOneType
