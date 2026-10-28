import Kk.B3OneGapCrossing
import SuccessorTree.V10.LevelRemovalSkipsOnly
import SuccessorTree.V10.KptCompleteSMTree
import SuccessorTree.EnvelopeMinimalityCore
import Mathlib.Tactic

/-!
# A forbidden singleton upper L-age forces an Algorithm 5.4 level

PR13 proved that the target of any *actual* one-gap Kpt boundary
crossing must satisfy the complete singleton upper-type B3 test.
Here we specialize the result to a map skipping exactly one level m
and to one original source prefix that it would have to cross.

Thus failure of the one-upper-type finite age test directly rules out
ANY genuine Kpt one-gap shape map making that crossing. This yields
the third disjunct of Algorithm 5.4's IsInterestingAt predicate for
a closure containing that original prefix, *without* a full
marked-to-auxiliary source spectrum comparison.

The finite numerical-H K4 witness at cut 22 remains to be given as
an actual age-test proof for its extracted type. This module does
not falsely assume that witness or the unresolved canonical-diary
embedding geometry.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuine one-gap Kpt map skipping m and taking a level-m node
to a specified level-(m+1) node forces the full finite L-only
single-upper-type B3 test at that target.

There is no hypothesis that the entire parameter-closed source
agrees with a chosen marked profile. -/
theorem skipsOnly_crossing_requires_single_upper_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (m : Nat) (hm : 0 < m) (hSkip : F.SkipsOnly m)
    (a b : AdmissibleKptNode family)
    (ha : LevelTree.lev a = m)
    (hb : LevelTree.lev b = m+1)
    (hCross : F a = b) :
    CommonSocleAgeTest family
      (prescribedOrdinarySocle (kptRecordAtLevel (m+1) b hb)) m
      (fun R => R = (kptRecordAtLevel (m+1) b hb).lReduct) := by
  have hqBound : m-1 ≤ LevelTree.lev a := by omega
  let q₀ : AdmissibleKptNode family :=
    LevelTree.ancestor a (m-1) hqBound
  have hqLevel : LevelTree.lev q₀ = m-1 :=
    LevelTree.level_ancestor a (m-1) hqBound
  have hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a := by
    rw [hqLevel, ha]
    omega
  have hFq : LevelTree.lev (F q₀) = m-1 := by
    rw [kptShapeMap_skipsOnly_level family F m hSkip q₀]
    rw [hqLevel]
    simp [show m-1 < m by omega]
  have hFa : LevelTree.lev (F a) = m+1 := by
    rw [hCross]
    exact hb
  have hgap : LevelTree.lev (F q₀) + 1 <
      LevelTree.lev (F a) := by omega
  have hb' : LevelTree.lev b =
      (LevelTree.lev (F a)-1)+1 := by omega
  have hGood :=
    genuine_gap_crossing_one_target_B3
      family F q₀ a b hprev hgap hb' hCross
  simpa [hFa] using hGood

/-- The contrapositive, in the form needed by the K4 first-gadget
witness: failure of the single upper-type finite L-age test
precludes ANY one-gap Kpt map crossing this genuine pair. -/
theorem bad_single_upper_precludes_onegap_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (m : Nat) (hm : 0 < m)
    (a b : AdmissibleKptNode family)
    (ha : LevelTree.lev a = m)
    (hb : LevelTree.lev b = m+1)
    (hBad : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle (kptRecordAtLevel (m+1) b hb)) m
      (fun R => R = (kptRecordAtLevel (m+1) b hb).lReduct)) :
    ¬ ∃ F : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F.SkipsOnly m ∧ F a = b := by
  rintro ⟨F,hSkip,hCross⟩
  exact hBad (skipsOnly_crossing_requires_single_upper_B3
    family F m hm hSkip a b ha hb hCross)

/-- If one seed node z in an actual closure has a forbidden finite
continuation using only its complete next L-type over cut m, the
level is ACTUALLY INTERESTING by clause I3: no monoid map can
skip m while realizing the required crossing for z.

The hypothesis is precisely the finite common-socle age-test
failure. It is NOT inferred from a graph-age inequality on the
selected shadow. -/
theorem bad_single_upper_forces_actual_interesting
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (z : AdmissibleKptNode family) (hzZ : z ∈ Z)
    (m : Nat) (hm : 0 < m)
    (hzm : m < LevelTree.lev z)
    (hBad : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (kptRecordAtLevel (m+1)
          (LevelTree.ancestor z (m+1) (Nat.succ_le_iff.mpr hzm))
          (LevelTree.level_ancestor z (m+1) (Nat.succ_le_iff.mpr hzm))))
      m
      (fun R => R =
        (kptRecordAtLevel (m+1)
          (LevelTree.ancestor z (m+1) (Nat.succ_le_iff.mpr hzm))
          (LevelTree.level_ancestor z (m+1) (Nat.succ_le_iff.mpr hzm))).lReduct)) :
    SuccessorTree.SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z m := by
  right
  right
  rintro ⟨D,hSkip,hAll⟩
  let a : AdmissibleKptNode family :=
    LevelTree.ancestor z m (Nat.le_of_lt hzm)
  let b : AdmissibleKptNode family :=
    LevelTree.ancestor z (m+1) (Nat.succ_le_iff.mpr hzm)
  have ha : LevelTree.lev a = m :=
    LevelTree.level_ancestor z m (Nat.le_of_lt hzm)
  have hb : LevelTree.lev b = m+1 :=
    LevelTree.level_ancestor z (m+1) (Nat.succ_le_iff.mpr hzm)
  have hCross : D a = b := hAll hzZ hzm
  have hForbidden :=
    skipsOnly_crossing_requires_single_upper_B3
      family D.map m hm hSkip a b ha hb hCross
  exact hBad hForbidden

end Kk
