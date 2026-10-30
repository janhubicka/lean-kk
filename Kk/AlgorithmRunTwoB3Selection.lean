import Kk.B3TwoAmbientOutputs
import Kk.AlgorithmRunSingleB3Selection
import Mathlib.Tactic

/-!
# Two actual ambient upper L-types force genuine AlgorithmRun selection

Unlike the single-upper proof, this theorem retains two complete
parameter-closed Kpt originals, which may have different upper L-types.
If their actual common-socle age test fails, a genuine one-gap map
cannot cross BOTH original prefixes simultaneously. This invokes
M2 boundary compatibility derived from their common ambient structure,
not a selected-shadow projection or frozen future-future L edges.

The theorem is still an I3 and AlgorithmRun bridge, not a claim about
all canonical resolved diaries or the final big Ramsey degree.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Failure of the actual common-socle B3 test for TWO named ambient
originals in a closure forces I3 at cut m. -/
theorem bad_two_ambient_upper_forces_actual_interesting
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v₀ v₁ : Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hZ₀ : A.kptOriginal family hAvoid v₀ ∈ Z)
    (hZ₁ : A.kptOriginal family hAvoid v₁ ∈ Z)
    (m : Nat) (hm : 0 < m)
    (hmFree₀ : m < A.freeLevel v₀.val)
    (hmFree₁ : m < A.freeLevel v₁.val)
    (hBad : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle (A.partialTypeAt (m+1) v₀.val)) m
      (fun T =>
        T = (A.partialTypeAt (m+1) v₀.val).lReduct ∨
        T = (A.partialTypeAt (m+1) v₁.val).lReduct)) :
    SuccessorTree.SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z m := by
  classical
  right
  right
  rintro ⟨D,hSkip,hAll⟩
  let z₀ : AdmissibleKptNode family := A.kptOriginal family hAvoid v₀
  let z₁ : AdmissibleKptNode family := A.kptOriginal family hAvoid v₁
  have hz₀ : m < LevelTree.lev z₀ := by
    change m < A.freeLevel v₀.val
    exact hmFree₀
  have hz₁ : m < LevelTree.lev z₁ := by
    change m < A.freeLevel v₁.val
    exact hmFree₁
  let a₀ : AdmissibleKptNode family :=
    LevelTree.ancestor z₀ m (Nat.le_of_lt hz₀)
  let a₁ : AdmissibleKptNode family :=
    LevelTree.ancestor z₁ m (Nat.le_of_lt hz₁)
  let b₀ : AdmissibleKptNode family :=
    LevelTree.ancestor z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  let b₁ : AdmissibleKptNode family :=
    LevelTree.ancestor z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have ha₀ : LevelTree.lev a₀ = m :=
    LevelTree.level_ancestor z₀ m (Nat.le_of_lt hz₀)
  have ha₁ : LevelTree.lev a₁ = m :=
    LevelTree.level_ancestor z₁ m (Nat.le_of_lt hz₁)
  have hb₀ : LevelTree.lev b₀ = m+1 :=
    LevelTree.level_ancestor z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  have hb₁ : LevelTree.lev b₁ = m+1 :=
    LevelTree.level_ancestor z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have hDa₀ : D a₀ = b₀ := hAll hZ₀ hz₀
  have hDa₁ : D a₁ = b₁ := hAll hZ₁ hz₁
  have hqBound : m-1 ≤ LevelTree.lev a₀ := by omega
  let q₀ : AdmissibleKptNode family :=
    LevelTree.ancestor a₀ (m-1) hqBound
  have hq : LevelTree.lev q₀ = m-1 :=
    LevelTree.level_ancestor a₀ (m-1) hqBound
  have hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀ := by omega
  have hFq : LevelTree.lev (D.map q₀) = m-1 := by
    rw [kptShapeMap_skipsOnly_level family D.map m hSkip q₀]
    rw [hq]
    simp [show m-1 < m by omega]
  have hFa₀ : LevelTree.lev (D.map a₀) = m+1 := by
    change LevelTree.lev (D a₀) = m+1
    rw [hDa₀]
    exact hb₀
  have hgap : LevelTree.lev (D.map q₀)+1 <
      LevelTree.lev (D.map a₀) := by omega
  have hbBelow₀ : b₀ ≤ z₀ :=
    LevelTree.ancestor_le z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  have hbBelow₁ : b₁ ≤ z₁ :=
    LevelTree.ancestor_le z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have hRaw₀ :
      b₀.val =
        (⟨m+1, A.partialTypeAt (m+1) v₀.val⟩ :
          RawPartialTypeNode db du dd) := by
    have h := kpt_prefix_raw_eq_ambient A family hAvoid v₀ b₀ hbBelow₀
    exact h.trans (congrArg
      (fun n : Nat =>
        (⟨n, A.partialTypeAt n v₀.val⟩ : RawPartialTypeNode db du dd))
      hb₀)
  have hRaw₁ :
      b₁.val =
        (⟨m+1, A.partialTypeAt (m+1) v₁.val⟩ :
          RawPartialTypeNode db du dd) := by
    have h := kpt_prefix_raw_eq_ambient A family hAvoid v₁ b₁ hbBelow₁
    exact h.trans (congrArg
      (fun n : Nat =>
        (⟨n, A.partialTypeAt n v₁.val⟩ : RawPartialTypeNode db du dd))
      hb₁)
  have hIndex : (LevelTree.lev (D.map a₀)-1)+1 = m+1 := by omega
  have hOut₀ :
      (D.map a₀).val =
        (⟨(LevelTree.lev (D.map a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (D.map a₀)-1)+1) v₀.val⟩ :
          RawPartialTypeNode db du dd) := by
    rw [hIndex]
    change (D a₀).val =
      (⟨m+1, A.partialTypeAt (m+1) v₀.val⟩ :
        RawPartialTypeNode db du dd)
    rw [hDa₀]
    exact hRaw₀
  have hOut₁ :
      (D.map a₁).val =
        (⟨(LevelTree.lev (D.map a₀)-1)+1,
          A.partialTypeAt ((LevelTree.lev (D.map a₀)-1)+1) v₁.val⟩ :
          RawPartialTypeNode db du dd) := by
    rw [hIndex]
    change (D a₁).val =
      (⟨m+1, A.partialTypeAt (m+1) v₁.val⟩ :
        RawPartialTypeNode db du dd)
    rw [hDa₁]
    exact hRaw₁
  have hGood :=
    genuine_gap_two_ambient_targets_B3
      family D.map q₀ a₀ hprev hgap a₁
      (ha₁.trans ha₀.symm) A v₀.val v₁.val hOut₀ hOut₁
  have hCut : LevelTree.lev (D.map a₀)-1 = m := by omega
  change CommonSocleAgeTest family
    (prescribedOrdinarySocle
      (A.partialTypeAt ((LevelTree.lev (D.map a₀)-1)+1) v₀.val))
    (LevelTree.lev (D.map a₀)-1)
    (fun T =>
      T = (A.partialTypeAt ((LevelTree.lev (D.map a₀)-1)+1) v₀.val).lReduct ∨
      T = (A.partialTypeAt ((LevelTree.lev (D.map a₀)-1)+1) v₁.val).lReduct)
    at hGood
  rw [hCut] at hGood
  exact hBad hGood

/-- A genuine Algorithm 5.4 run must retain any level with an actual
two-upper B3 failure on names in its FULL selected closure. -/
theorem algorithmRun_selects_actual_failed_two_upper_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v₀ v₁ : Fin A.size)
    (m : Nat) (hm : 0 < m)
    (hmFree₀ : m < A.freeLevel v₀.val)
    (hmFree₁ : m < A.freeLevel v₁.val)
    (hBad : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle (A.partialTypeAt (m+1) v₀.val)) m
      (fun T =>
        T = (A.partialTypeAt (m+1) v₀.val).lReduct ∨
        T = (A.partialTypeAt (m+1) v₁.val).lReduct))
    (X : Set (AdmissibleKptNode family))
    (ell : Nat) (hmEll : m < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hC₀ : A.kptOriginal family hAvoid v₀ ∈
      SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X)
    (hC₁ : A.kptOriginal family hAvoid v₁ ∈
      SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X) :
    m ∈ R.I m := by
  have hInteresting :=
    bad_two_ambient_upper_forces_actual_interesting
      family A hAvoid v₀ v₁
      (SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (m+1)) X)
      hC₀ hC₁ m hm hmFree₀ hmFree₁ hBad
  have hSelected := (R.interesting_step m hmEll hInteresting).1
  rw [hSelected]
  simp

end Kk
