import SuccessorTree.V10.CompleteNextColumn
import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# Equal ordinary cut bits determine the complete next L+/E type

English proof and independent review precede this reconstruction in
`docs/audits/2026-11-23-upper-reconstruction-english.md`.

All six fields of the next column are retained. The common ordinary cut
bit may be true or false. Deriving its equality from the actual full
stage geometry is a separate application obligation.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Explicit extensionality of the SIX fields of a complete new
L+/E column. The upstream library has a structure but does not
register an extensionality theorem for it. No new axioms. -/
private theorem equalCutCompleteNextColumn_eq_of_fields
    {ell db du dd : Nat}
    (S T : CompleteNextColumn ell db du dd)
    (hTo : S.toNew = T.toNew)
    (hFrom : S.fromNew = T.fromNew)
    (hETo : S.eToNew = T.eToNew)
    (hEFrom : S.eFromNew = T.eFromNew)
    (hUnary : S.unaryNew = T.unaryNew)
    (hDiagonal : S.diagonalNew = T.diagonalNew) :
    S = T := by
  cases S with
  | mk t f et ef u d =>
    cases T with
    | mk t' f' et' ef' u' d' =>
      dsimp at hTo hFrom hETo hEFrom hUnary hDiagonal
      cases hTo
      cases hFrom
      cases hETo
      cases hEFrom
      cases hUnary
      cases hDiagonal
      rfl

/-- Two genuinely eligible original future vertices in ONE enumerated
L+/E graph structure with symmetric ordinary L, equal complete old
dependent types and equal ordinary cut bits have identical
complete next dependent types. The auxiliary E cut bit is TRUE on
both sides and reverse E is FALSE. There are no other new atoms.

This is a complete L+/E raw-type uniqueness assertion, not a
selected-front graph-age comparison. -/
theorem full_equal_ordinary_cut_column_determines_next_type
    (A : EnumeratedPartialStructure 1 0 1)
    (hSym : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1))
    (cut : Nat) (v w : Fin A.size)
    (hFreeV : cut+1 ≤ A.freeLevel v.val)
    (hFreeW : cut+1 ≤ A.freeLevel w.val)
    (hCutBit : A.L.binary cut v.val (0 : Fin 1) =
      A.L.binary cut w.val (0 : Fin 1))
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
  have hNewTo : Q.nextColumn.toNew = R.nextColumn.toNew := by
    funext x r
    cases x with
    | none =>
      fin_cases r
      change A.L.binary v.val cut (0 : Fin 1) =
        A.L.binary w.val cut (0 : Fin 1)
      exact (hSym v.val cut).trans (hCutBit.trans (hSym w.val cut).symm)
    | some x =>
      rfl
  have hNewFrom : Q.nextColumn.fromNew = R.nextColumn.fromNew := by
    funext x r
    cases x with
    | none =>
      fin_cases r
      change A.L.binary cut v.val (0 : Fin 1) =
        A.L.binary cut w.val (0 : Fin 1)
      exact hCutBit
    | some x =>
      rfl
  have hNewETo : Q.nextColumn.eToNew = R.nextColumn.eToNew := by
    funext x
    cases x with
    | none =>
      change A.E v.val cut = A.E w.val cut
      rw [hReverseV, hReverseW]
    | some x =>
      rfl
  have hNewEFrom : Q.nextColumn.eFromNew = R.nextColumn.eFromNew := by
    funext x
    cases x with
    | none =>
      change A.E cut v.val = A.E cut w.val
      rw [hForwardV, hForwardW]
    | some x =>
      rfl
  have hNewUnary : Q.nextColumn.unaryNew = R.nextColumn.unaryNew := by
    funext r
    exact Fin.elim0 r
  have hNewDiagonal : Q.nextColumn.diagonalNew = R.nextColumn.diagonalNew := by
    funext r
    rfl
  have hNextColumn : Q.nextColumn = R.nextColumn :=
    equalCutCompleteNextColumn_eq_of_fields
      Q.nextColumn R.nextColumn
      hNewTo hNewFrom hNewETo hNewEFrom hNewUnary hNewDiagonal
  exact completeNextColumn_determines_type Q R
    hOldRestriction hNextColumn

#print axioms Kk.full_equal_ordinary_cut_column_determines_next_type

end Kk
