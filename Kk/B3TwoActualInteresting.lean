import Kk.B3TwoAmbientOutputs
import Kk.B3OneGapInteresting
import SuccessorTree.V10.ConcreteOriginalPool
import Mathlib.Tactic

/-!
# Two actual ambient Kpt upper types force Algorithm 5.4 interest

Suppose two full Kpt originals of the SAME forbidden-free finite
partial structure belong to the parameter-closed stage Z and extend
strictly above cut m. If a finite L-only corrected B3 continuation
using JUST their two complete next L-types makes a forbidden
configuration appear at m, then NO genuine Kpt one-gap ShapeMap
can skip m while matching every crossing of Z.

The proof extracts the two genuine source prefixes a0,a1 at level m
and their next prefixes b0,b1 at m+1. A hypothetical one-gap map
crosses both. By the actual one-gap level function, its images of
a0 and a1 have level m+1, and its predecessor of a0 stays at m-1.
Its two complete output raw records equal the literal (m+1)-types
of the chosen original ambient vertices, including every E bit.
The two-boundary theorem of B3TwoAmbientOutputs then rules out
the finite forbidden continuation.

This proves the ACTUAL third clause of Algorithm 5.4's
IsInterestingAt, without a selected graph-age shadow projection
or a hidden source-spectrum assumption. It is completely generic
in the normalized finite relational language.

Application to K4 numerical H: the selected top original at 38
and auxiliary original at 22 are both in Z at cut 10 (checked
separately from AlgorithmRun), and the two-complete-upper-type
B3 continuation genuinely fails (checked in K4NumericalHCut10Transfer).
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Genuine two-complete-upper-type B3 failure forces the
ACTUAL Algorithm 5.4 interesting-level predicate on any
closure containing both original nodes. No I1/I2 hypothesis is
needed: the explicit obstruction establishes I3 directly. -/
theorem bad_two_ambient_upper_forces_actual_interesting
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v₀ v₁ : Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hZ₀ : A.kptOriginal family hAvoid v₀ ∈ Z)
    (hZ₁ : A.kptOriginal family hAvoid v₁ ∈ Z)
    (m : Nat) (hmPos : 0 < m)
    (hmFree₀ : m < A.freeLevel v₀.val)
    (hmFree₁ : m < A.freeLevel v₁.val)
    (hFailed : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle (A.partialTypeAt (m+1) v₀.val)) m
      (fun R => R = (A.partialTypeAt (m+1) v₀.val).lReduct ∨
        R = (A.partialTypeAt (m+1) v₁.val).lReduct)) :
    SuccessorTree.SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z m := by
  classical
  right
  right
  rintro ⟨D,hSkip,hCrossAll⟩
  let z₀ : AdmissibleKptNode family := A.kptOriginal family hAvoid v₀
  let z₁ : AdmissibleKptNode family := A.kptOriginal family hAvoid v₁
  have hz₀ : m < LevelTree.lev z₀ := hmFree₀
  have hz₁ : m < LevelTree.lev z₁ := hmFree₁
  let a₀ := LevelTree.ancestor z₀ m (Nat.le_of_lt hz₀)
  let a₁ := LevelTree.ancestor z₁ m (Nat.le_of_lt hz₁)
  let b₀ := LevelTree.ancestor z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  let b₁ := LevelTree.ancestor z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have ha₀ : LevelTree.lev a₀ = m :=
    LevelTree.level_ancestor z₀ m (Nat.le_of_lt hz₀)
  have ha₁ : LevelTree.lev a₁ = m :=
    LevelTree.level_ancestor z₁ m (Nat.le_of_lt hz₁)
  have hb₀ : LevelTree.lev b₀ = m+1 :=
    LevelTree.level_ancestor z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  have hb₁ : LevelTree.lev b₁ = m+1 :=
    LevelTree.level_ancestor z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have hCross₀ : D a₀ = b₀ := hCrossAll hZ₀ hz₀
  have hCross₁ : D a₁ = b₁ := hCrossAll hZ₁ hz₁
  let q₀ := LevelTree.ancestor a₀ (m-1) (by omega)
  have hqLevel : LevelTree.lev q₀ = m-1 :=
    LevelTree.level_ancestor a₀ (m-1) (by omega)
  have hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀ := by
    rw [hqLevel,ha₀]
    omega
  have hDqLevel : LevelTree.lev (D q₀) = m-1 := by
    rw [kptShapeMap_skipsOnly_level family D.map m hSkip q₀]
    rw [hqLevel]
    simp [show m-1 < m by omega]
  have hD₀Level : LevelTree.lev (D a₀) = m+1 := by
    rw [hCross₀]
    exact hb₀
  have hgap : LevelTree.lev (D q₀)+1 <
      LevelTree.lev (D a₀) := by omega
  have hlev₁ : LevelTree.lev a₁ = LevelTree.lev a₀ :=
    ha₁.trans ha₀.symm
  have hb₀Below : b₀ ≤ z₀ :=
    LevelTree.ancestor_le z₀ (m+1) (Nat.succ_le_iff.mpr hz₀)
  have hb₁Below : b₁ ≤ z₁ :=
    LevelTree.ancestor_le z₁ (m+1) (Nat.succ_le_iff.mpr hz₁)
  have hRaw₀ : b₀.val =
      (⟨m+1,A.partialTypeAt (m+1) v₀.val⟩ :
        RawPartialTypeNode db du dd) := by
    have h := kpt_prefix_raw_eq_ambient A family hAvoid v₀ b₀ hb₀Below
    exact h.trans
      (congrArg (fun n : Nat =>
        (⟨n,A.partialTypeAt n v₀.val⟩ : RawPartialTypeNode db du dd)) hb₀)
  have hRaw₁ : b₁.val =
      (⟨m+1,A.partialTypeAt (m+1) v₁.val⟩ :
        RawPartialTypeNode db du dd) := by
    have h := kpt_prefix_raw_eq_ambient A family hAvoid v₁ b₁ hb₁Below
    exact h.trans
      (congrArg (fun n : Nat =>
        (⟨n,A.partialTypeAt n v₁.val⟩ : RawPartialTypeNode db du dd)) hb₁)
  have hDcut : (LevelTree.lev (D a₀)-1)+1 = m+1 := by
    omega
  have hOutput₀ : (D a₀).val =
      (⟨(LevelTree.lev (D a₀)-1)+1,
        A.partialTypeAt ((LevelTree.lev (D a₀)-1)+1) v₀.val⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      (D a₀).val = b₀.val := congrArg Subtype.val hCross₀
      _ = (⟨m+1,A.partialTypeAt (m+1) v₀.val⟩ :
          RawPartialTypeNode db du dd) := hRaw₀
      _ = _ := (congrArg (fun n : Nat =>
        (⟨n,A.partialTypeAt n v₀.val⟩ : RawPartialTypeNode db du dd)) hDcut).symm
  have hOutput₁ : (D a₁).val =
      (⟨(LevelTree.lev (D a₀)-1)+1,
        A.partialTypeAt ((LevelTree.lev (D a₀)-1)+1) v₁.val⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      (D a₁).val = b₁.val := congrArg Subtype.val hCross₁
      _ = (⟨m+1,A.partialTypeAt (m+1) v₁.val⟩ :
          RawPartialTypeNode db du dd) := hRaw₁
      _ = _ := (congrArg (fun n : Nat =>
        (⟨n,A.partialTypeAt n v₁.val⟩ : RawPartialTypeNode db du dd)) hDcut).symm
  have hM : LevelTree.lev (D a₀)-1 = m := by omega
  have hFailedActual : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (A.partialTypeAt ((LevelTree.lev (D a₀)-1)+1) v₀.val))
      (LevelTree.lev (D a₀)-1)
      (fun R =>
        R = (A.partialTypeAt
          ((LevelTree.lev (D a₀)-1)+1) v₀.val).lReduct ∨
        R = (A.partialTypeAt
          ((LevelTree.lev (D a₀)-1)+1) v₁.val).lReduct) := by
    simpa only [hM] using hFailed
  exact bad_two_ambient_targets_contradicts_genuine_gap
    family D.map q₀ a₀ hprev hgap a₁ hlev₁
    A v₀.val v₁.val hOutput₀ hOutput₁ hFailedActual

end Kk
