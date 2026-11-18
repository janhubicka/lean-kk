import SuccessorTree.V10.CompleteNextColumn
import Kk.NumericHIndexedUpperRecords
import Mathlib.Tactic

/-!
# Track D: a zero ordinary-L new column fixes the complete dependent L+/E type

English-first mathematical proof and adversarial audit were committed BEFORE
Lean code: docs/audits/2026-11-18-track-d-zero-full-column-english.md.

Every auxiliary E bit and BOTH directed ordinary L orientations are retained.
This theorem is local to ONE actual EnumeratedPartialStructure; no new
E is assigned to L-only forbidden clique continuations. It proves neither
an actual full no-I1 terminal predicate nor a global diary theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two genuinely eligible original future vertices in ONE enumerated
L+/E graph structure with symmetric ordinary L, equal complete old
dependent types and both ordinary cut bits ZERO have identical
complete next dependent types. The auxiliary E cut bit is TRUE on
both sides and reverse E is FALSE. There are no other new atoms.

This is a complete L+/E raw-type uniqueness assertion, not a
selected-front graph-age comparison. -/
theorem full_zero_ordinary_cut_column_determines_next_type
    (A : EnumeratedPartialStructure 1 0 1)
    (hSym : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1))
    (cut : Nat) (v w : Fin A.size)
    (hFreeV : cut+1 ≤ A.freeLevel v.val)
    (hFreeW : cut+1 ≤ A.freeLevel w.val)
    (hZeroV : A.L.binary cut v.val (0 : Fin 1) = false)
    (hZeroW : A.L.binary cut w.val (0 : Fin 1) = false)
    (hOld : A.partialTypeAt cut v.val =
      A.partialTypeAt cut w.val) :
    A.partialTypeAt (cut+1) v.val =
      A.partialTypeAt (cut+1) w.val := by
  let Q : PartialTypeWithE (cut+1) 1 0 1 :=
    A.partialTypeAt (cut+1) v.val
  let R : PartialTypeWithE (cut+1) 1 0 1 :=
    A.partialTypeAt (cut+1) w.val
  have hOldRestriction :
      Q.restrict (Nat.le_succ cut) =
        R.restrict (Nat.le_succ cut) := by
    calc
      Q.restrict (Nat.le_succ cut) =
          A.partialTypeAt cut v.val :=
        A.partialTypeAt_restrict cut (cut+1) v.val
          (Nat.le_succ cut)
      _ = A.partialTypeAt cut w.val := hOld
      _ = R.restrict (Nat.le_succ cut) :=
        (A.partialTypeAt_restrict cut (cut+1) w.val
          (Nat.le_succ cut)).symm
  have hReverseV : A.E v.val cut = false := by
    have h := A.partialTypeAt_no_reverseE
      (cut+1) v.val hFreeV (Fin.last cut)
    change A.E v.val cut = false at h
    exact h
  have hReverseW : A.E w.val cut = false := by
    have h := A.partialTypeAt_no_reverseE
      (cut+1) w.val hFreeW (Fin.last cut)
    change A.E w.val cut = false at h
    exact h
  have hForwardV : A.E cut v.val = true :=
    (A.E_iff_freeLevel cut v.val).2 (by omega)
  have hForwardW : A.E cut w.val = true :=
    (A.E_iff_freeLevel cut w.val).2 (by omega)
  have hNextColumn : Q.nextColumn = R.nextColumn := by
    apply CompleteNextColumn.ext
    · funext x r
      cases x with
      | none =>
        fin_cases r
        change A.L.binary v.val cut (0 : Fin 1) =
          A.L.binary w.val cut (0 : Fin 1)
        rw [hSym v.val cut, hSym w.val cut, hZeroV, hZeroW]
      | some x =>
        rfl
    · funext x r
      cases x with
      | none =>
        fin_cases r
        change A.L.binary cut v.val (0 : Fin 1) =
          A.L.binary cut w.val (0 : Fin 1)
        rw [hZeroV, hZeroW]
      | some x =>
        rfl
    · funext x
      cases x with
      | none =>
        change A.E v.val cut = A.E w.val cut
        rw [hReverseV, hReverseW]
      | some x =>
        rfl
    · funext x
      cases x with
      | none =>
        change A.E cut v.val = A.E cut w.val
        rw [hForwardV, hForwardW]
      | some x =>
        rfl
    · funext r
      exact Fin.elim0 r
    · funext r
      rfl
  exact completeNextColumn_determines_type Q R
    hOldRestriction hNextColumn

#print axioms Kk.full_zero_ordinary_cut_column_determines_next_type

end Kk
