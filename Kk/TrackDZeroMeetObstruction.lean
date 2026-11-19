import Kk.TrackDZeroFullColumn
import Kk.NumericHI2FullFork
import Mathlib.Tactic

/-!
# Track D: no strict meet of two actual eligible zero-L originals at an even cut

English-first complete proof and 20 hostile checks:
docs/audits/2026-11-18-track-d-all-stage-zero-no-i1-english.md

The stage-normal-form reduction says every nonseed even-real Kpt
terminal is a meet of two ACTUAL original full dependent types.
This module proves the core impossibility when both originals
genuinely reach the tested cut and have zero ordinary cut L:
same old raw prefix plus zero L and forced E gives identical
next raw prefix, whereas a meet at exactly cut would force
different next ancestors.

The theorem does not presume the originals belong to a live Kpt
crossing source, does not infer seed absence or the global diary
Plan shape, and does not attach artificial E to an L-only witness.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two actual Kpt originals in ONE ambient A, each with free
E-level strictly beyond cut and zero ordinary L at cut, cannot
have their TRUE same-component meet end exactly at cut, assuming
A.L symmetric. This uses the full dependent L+/E next-column
uniqueness theorem; it works EVEN WHEN those original types are
not themselves members of a smaller selected Kpt source. -/
theorem actual_zero_cut_originals_meet_level_ne_cut
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hSym : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (cut : Nat) (v w : Fin A.size)
    (hFreeV : cut+1 ≤ A.freeLevel v.val)
    (hFreeW : cut+1 ≤ A.freeLevel w.val)
    (hZeroV : A.L.binary cut v.val (0 : Fin 1) = false)
    (hZeroW : A.L.binary cut w.val (0 : Fin 1) = false)
    (hComp : SMTree.Envelope.SameComponent
      (A.kptOriginal family hAvoid v)
      (A.kptOriginal family hAvoid w)) :
    LevelTree.lev
      (LevelTree.meet
        (A.kptOriginal family hAvoid v)
        (A.kptOriginal family hAvoid w)) ≠ cut := by
  let a : AdmissibleKptNode family := A.kptOriginal family hAvoid v
  let b : AdmissibleKptNode family := A.kptOriginal family hAvoid w
  intro hMeet
  have hLevA : cut < LevelTree.lev a := by
    change cut < A.freeLevel v.val
    omega
  have hLevB : cut < LevelTree.lev b := by
    change cut < A.freeLevel w.val
    omega
  have hMeetA :
      LevelTree.meet a b =
        LevelTree.ancestor a cut (Nat.le_of_lt hLevA) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_left hComp) hMeet (Nat.le_of_lt hLevA)
  have hMeetB :
      LevelTree.meet a b =
        LevelTree.ancestor b cut (Nat.le_of_lt hLevB) :=
    LevelTree.eq_ancestor_of_le
      (LevelTree.meet_le_right hComp) hMeet (Nat.le_of_lt hLevB)
  have hOldAnc :
      LevelTree.ancestor a cut (Nat.le_of_lt hLevA) =
        LevelTree.ancestor b cut (Nat.le_of_lt hLevB) :=
    hMeetA.symm.trans hMeetB
  have hNextAncNe :
      LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA) ≠
      LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB) := by
    intro hNext
    have hCommon :
        LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hLevA) ≤ LevelTree.meet a b := by
      apply LevelTree.le_meet
      · exact LevelTree.ancestor_le a (cut+1)
          (Nat.succ_le_iff.mpr hLevA)
      · rw [hNext]
        exact LevelTree.ancestor_le b (cut+1)
          (Nat.succ_le_iff.mpr hLevB)
    have hLev := LevelTree.level_le_of_le hCommon
    have hAncLev := LevelTree.level_ancestor
      a (cut+1) (Nat.succ_le_iff.mpr hLevA)
    have hMeetLevel : LevelTree.lev (LevelTree.meet a b) = cut := by
      simpa only [a, b] using hMeet
    have hImpossible : cut + 1 ≤ cut := by
      calc
        cut + 1 =
            LevelTree.lev
              (LevelTree.ancestor a (cut+1)
                (Nat.succ_le_iff.mpr hLevA)) := hAncLev.symm
        _ ≤ LevelTree.lev (LevelTree.meet a b) := hLev
        _ = cut := hMeetLevel
    omega
  have hOldA :
      (LevelTree.ancestor a cut (Nat.le_of_lt hLevA)).val =
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v a (by exact le_rfl)
      cut (Nat.le_of_lt hLevA)
  have hOldB :
      (LevelTree.ancestor b cut (Nat.le_of_lt hLevB)).val =
        (⟨cut,A.partialTypeAt cut w.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w b (by exact le_rfl)
      cut (Nat.le_of_lt hLevB)
  have hPhysicalOld :
      A.partialTypeAt cut v.val = A.partialTypeAt cut w.val := by
    have hRaw :
        (⟨cut,A.partialTypeAt cut v.val⟩ :
          RawPartialTypeNode 1 0 1) =
        (⟨cut,A.partialTypeAt cut w.val⟩ :
          RawPartialTypeNode 1 0 1) := by
      calc
        (⟨cut,A.partialTypeAt cut v.val⟩ :
            RawPartialTypeNode 1 0 1) =
            (LevelTree.ancestor a cut (Nat.le_of_lt hLevA)).val :=
          hOldA.symm
        _ = (LevelTree.ancestor b cut (Nat.le_of_lt hLevB)).val :=
          congrArg Subtype.val hOldAnc
        _ = (⟨cut,A.partialTypeAt cut w.val⟩ :
            RawPartialTypeNode 1 0 1) := hOldB
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hPhysicalNext :
      A.partialTypeAt (cut+1) v.val =
        A.partialTypeAt (cut+1) w.val :=
    full_zero_ordinary_cut_column_determines_next_type
      A hSym cut v w hFreeV hFreeW hZeroV hZeroW hPhysicalOld
  have hUpperA :
      (LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid v a (by exact le_rfl)
      (cut+1) (Nat.succ_le_iff.mpr hLevA)
  have hUpperB :
      (LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) w.val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid w b (by exact le_rfl)
      (cut+1) (Nat.succ_le_iff.mpr hLevB)
  have hNextAnc :
      LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hLevA) =
      LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hLevB) := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor a (cut+1)
          (Nat.succ_le_iff.mpr hLevA)).val =
          (⟨cut+1,A.partialTypeAt (cut+1) v.val⟩ :
            RawPartialTypeNode 1 0 1) := hUpperA
      _ = (⟨cut+1,A.partialTypeAt (cut+1) w.val⟩ :
            RawPartialTypeNode 1 0 1) := by rw [hPhysicalNext]
      _ = (LevelTree.ancestor b (cut+1)
          (Nat.succ_le_iff.mpr hLevB)).val := hUpperB.symm
  exact hNextAncNe hNextAnc

#print axioms Kk.actual_zero_cut_originals_meet_level_ne_cut

end Kk
