import Kk.TrackDZeroFullColumn
import Kk.NumericHI2FullFork
import Kk.NumericHFullClosureCrossing
import Mathlib.Tactic

/-!
# Track D: genuine full zero ordinary cut-star excludes all strict Kpt I2 forks

English-first proof and 18 hostile checks committed BEFORE Lean:
docs/audits/2026-11-18-track-d-zero-star-full-no-i2-english.md

The actual SAME Kpt crossing node and SAME finite physical original
provide complete old/upper dependent L+/E ancestors. With zero
ordinary-L cut bits on EVERY full source representative, the complete
next column is uniquely determined by the complete old type.
This excludes full strictly crossing forks WITHOUT no-I1. The
reverse I2-meet conclusion still needs no-I1 to exclude trivial
meet(a,a) at an actual level-c terminal.

No selected diary shadow, invented E on L-only witnesses, or
global Kk-free degree claim is involved.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Any genuine complete Kpt source Z exhaustively represented by
finite original-name addresses inside ONE actual symmetric graph A
has no strict full old-equal/next-different L+/E crossing fork if
every genuinely represented eligible source has ordinary L(c,v)=0.

Includes ALL generated Kpt parameter and meet nodes. The original
name list need not be injective on types; no I1 or I2 is assumed. -/
theorem full_kpt_cut_fork_false_of_zero_full_physical_star
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hSym : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    {M : Nat}
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hZero : ∀ v : Fin M,
      closureSelectedOriginal family A hAvoid original Z cut v →
      cut+1 ≤ A.freeLevel (original v).val →
      A.L.binary cut (original v).val (0 : Fin 1) = false) :
    ¬ KptFullCutFork family Z cut := by
  classical
  rintro ⟨a,ha,b,hb,hCa,hCb,hOldEq,hUpperNe⟩
  obtain ⟨va,hBelowA⟩ := hPool a ha
  obtain ⟨vb,hBelowB⟩ := hPool b hb
  have hFreeA : cut+1 ≤ A.freeLevel (original va).val := by
    have h := kptBelowOriginal_level_le_free
      family A hAvoid (original va) a hBelowA
    omega
  have hFreeB : cut+1 ≤ A.freeLevel (original vb).val := by
    have h := kptBelowOriginal_level_le_free
      family A hAvoid (original vb) b hBelowB
    omega
  have hFullA :
      closureSelectedOriginal family A hAvoid original Z cut va :=
    ⟨a,ha,hCa,hBelowA⟩
  have hFullB :
      closureSelectedOriginal family A hAvoid original Z cut vb :=
    ⟨b,hb,hCb,hBelowB⟩
  have hZeroA := hZero va hFullA hFreeA
  have hZeroB := hZero vb hFullB hFreeB
  have hAncOldA :
      (LevelTree.ancestor a cut (Nat.le_of_lt hCa)).val =
        (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original va) a hBelowA cut (Nat.le_of_lt hCa)
  have hAncOldB :
      (LevelTree.ancestor b cut (Nat.le_of_lt hCb)).val =
        (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original vb) b hBelowB cut (Nat.le_of_lt hCb)
  have hOldRawA :
      kptFullOldAtCut a cut =
        some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullOldAtCut a cut =
          some (LevelTree.ancestor a cut (Nat.le_of_lt hCa)).val :=
        (kpt_full_old_upper_types_of_crossing a cut hCa).1
      _ = some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncOldA
  have hOldRawB :
      kptFullOldAtCut b cut =
        some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullOldAtCut b cut =
          some (LevelTree.ancestor b cut (Nat.le_of_lt hCb)).val :=
        (kpt_full_old_upper_types_of_crossing b cut hCb).1
      _ = some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncOldB
  have hSomeOld :
      some (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) =
        some (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    hOldRawA.symm.trans (hOldEq.trans hOldRawB)
  have hPhysicalOld :
      A.partialTypeAt cut (original va).val =
        A.partialTypeAt cut (original vb).val := by
    have hRaw :
        (⟨cut,A.partialTypeAt cut (original va).val⟩ :
          RawPartialTypeNode 1 0 1) =
        (⟨cut,A.partialTypeAt cut (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
      Option.some.inj hSomeOld
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  have hPhysicalUpper :
      A.partialTypeAt (cut+1) (original va).val =
        A.partialTypeAt (cut+1) (original vb).val :=
    full_zero_ordinary_cut_column_determines_next_type
      A hSym cut (original va) (original vb)
      hFreeA hFreeB hZeroA hZeroB hPhysicalOld
  have hAncUpA :
      (LevelTree.ancestor a (cut+1)
        (Nat.succ_le_iff.mpr hCa)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original va) a hBelowA (cut+1)
        (Nat.succ_le_iff.mpr hCa)
  have hAncUpB :
      (LevelTree.ancestor b (cut+1)
        (Nat.succ_le_iff.mpr hCb)).val =
        (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original vb) b hBelowB (cut+1)
        (Nat.succ_le_iff.mpr hCb)
  have hNextA :
      kptFullUpperAtCut a cut =
        some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullUpperAtCut a cut =
          some (LevelTree.ancestor a (cut+1)
            (Nat.succ_le_iff.mpr hCa)).val :=
        (kpt_full_old_upper_types_of_crossing a cut hCa).2
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncUpA
  have hNextB :
      kptFullUpperAtCut b cut =
        some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) := by
    calc
      kptFullUpperAtCut b cut =
          some (LevelTree.ancestor b (cut+1)
            (Nat.succ_le_iff.mpr hCb)).val :=
        (kpt_full_old_upper_types_of_crossing b cut hCb).2
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
          RawPartialTypeNode 1 0 1) :=
        congrArg some hAncUpB
  have hUpperEq :
      kptFullUpperAtCut a cut = kptFullUpperAtCut b cut := by
    calc
      kptFullUpperAtCut a cut =
          some (⟨cut+1,A.partialTypeAt (cut+1) (original va).val⟩ :
            RawPartialTypeNode 1 0 1) := hNextA
      _ = some (⟨cut+1,A.partialTypeAt (cut+1) (original vb).val⟩ :
            RawPartialTypeNode 1 0 1) := by rw [hPhysicalUpper]
      _ = kptFullUpperAtCut b cut := hNextB.symm
  exact hUpperNe hUpperEq

/-- The exact no-I1 -> no-I2 consequence of zero full physical
cut-star. The no-I1 premise is essential because self-meets
at a terminal node can be an I2 test without a strict fork. -/
theorem full_kpt_no_i2_of_no_i1_and_zero_full_physical_star
    (family : List (NormalizedForbidden 1 0 1))
    (A : EnumeratedPartialStructure 1 0 1)
    (hSym : ∀ i j : Nat,
      A.L.binary i j (0 : Fin 1) =
        A.L.binary j i (0 : Fin 1))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    {M : Nat}
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hZero : ∀ v : Fin M,
      closureSelectedOriginal family A hAvoid original Z cut v →
      cut+1 ≤ A.freeLevel (original v).val →
      A.L.binary cut (original v).val (0 : Fin 1) = false)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) :
    ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut := by
  intro hI2
  have hFork : KptFullCutFork family Z cut :=
    (kpt_no_I1_I2_iff_complete_full_fork family Z cut hNoI1).mp hI2
  exact (full_kpt_cut_fork_false_of_zero_full_physical_star
    family A hSym hAvoid original Z hPool cut hZero) hFork

#print axioms Kk.full_kpt_cut_fork_false_of_zero_full_physical_star
#print axioms Kk.full_kpt_no_i2_of_no_i1_and_zero_full_physical_star

end Kk
