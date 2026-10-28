import Kk.B3SkipNecessity
import SuccessorTree.V10.M2BoundaryFinalCriterion
import Mathlib.Tactic

/-!
# Genuine one-gap Kpt maps cannot cross a single forbidden upper type

Every actual Kpt shape map whose images have a first consecutive
source-level gap has a finite L-only B3 age certificate on its genuine
boundary family (M2BoundaryCompatibleB3Closure).

This module extracts the B3 test for ONE genuine boundary upper type.
In particular, the boundary need not have the same full source as the
proposed macro-diary; a forbidden finite continuation using repetitions
of just one complete upper L-type already obstructs a one-gap crossing,
provided that upper type is the exact image of a source boundary node.

The theorem does NOT construct an actual Algorithm 5.4 selected level,
nor assert the numerical H first-gadget type is in the boundary.
Those are separate application/geometry tasks.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The actual target type of one genuine Kpt boundary node passes
the full finite corrected B3 test when repeated arbitrarily many
times in a continuation over its own ordinary L-socle.

This is strictly a *single-image* age-test necessity theorem. No
equality of full marked and auxiliary source families is assumed. -/
theorem genuine_gap_boundary_one_target_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (Q : PartialTypeWithE ((LevelTree.lev (F a₀)-1)+1) db du dd)
    (hImage : (F a₀).val =
      (⟨(LevelTree.lev (F a₀)-1)+1,Q⟩ :
        RawPartialTypeNode db du dd)) :
    CommonSocleAgeTest family
      (prescribedOrdinarySocle Q) (LevelTree.lev (F a₀)-1)
      (fun R => R = Q.lReduct) := by
  classical
  let idx : M2BoundaryIndex family a₀ := ⟨a₀, rfl⟩
  let P : PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd :=
    m2Boundary_prescribedData family F q₀ a₀ hprev hgap
  let S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd :=
    m2Boundary_sourceType family F q₀ a₀ hprev hgap idx
  have hSource : S0 ∈ P.source :=
    m2Boundary_prescribed_source family F q₀ a₀ hprev hgap idx
  have hTarget : P.target S0 = Q := by
    have hBoundary :
        P.target S0 =
          m2Boundary_targetType family F q₀ a₀ hprev hgap idx :=
      m2Boundary_prescribed_target family F q₀ a₀ hprev hgap idx
    have hRaw : (F a₀).val =
        (⟨(LevelTree.lev (F a₀)-1)+1,P.target S0⟩ :
          RawPartialTypeNode db du dd) := by
      rw [hBoundary]
      exact m2Boundary_target_raw family F q₀ a₀ hprev hgap idx
    have hCodes :
        (⟨(LevelTree.lev (F a₀)-1)+1,P.target S0⟩ :
          RawPartialTypeNode db du dd) =
        (⟨(LevelTree.lev (F a₀)-1)+1,Q⟩ :
          RawPartialTypeNode db du dd) :=
      hRaw.symm.trans hImage
    exact eq_of_heq (Sigma.mk.inj_iff.mp hCodes).2
  have hB3 : P.CompatibleB3 family :=
    m2Boundary_actual_compatibleB3 family F q₀ a₀ hprev hgap
  intro W hFinite hSame hUpper hDelete bad hBad
  have hSameP :
      SameInitialL W (prescribedOrdinarySocle (P.target S0))
        (LevelTree.lev (F a₀)-1) := by
    rw [hTarget]
    exact hSame
  have hUpperP :
      UpperTypesPrescribed W (LevelTree.lev (F a₀)-1)
        (P.CompatibleUpperLType S0) := by
    intro x hx hAbove
    refine ⟨S0,hSource,sameOrdinaryAtCut_refl S0,?_⟩
    rw [hTarget]
    exact hUpper x hx hAbove
  exact hB3 S0 hSource W hFinite hSameP hUpperP hDelete bad hBad

/-- Paper-facing form: if a genuine Kpt shape map maps a boundary
node a0 to b, the entire finite L-age test for the *complete*
L-reduct of b holds over the target's initial ordinary L-socle.
No requirement on other boundary source types remains.

When a proposed gap is used to skip a selected numerical H cut,
its required source/target crossing supplies this exact hImage. -/
theorem genuine_gap_crossing_one_target_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ b : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (hb : LevelTree.lev b = (LevelTree.lev (F a₀)-1)+1)
    (hCross : F a₀ = b) :
    CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (kptRecordAtLevel ((LevelTree.lev (F a₀)-1)+1) b hb))
      (LevelTree.lev (F a₀)-1)
      (fun R => R =
        (kptRecordAtLevel ((LevelTree.lev (F a₀)-1)+1) b hb).lReduct) := by
  have hImage : (F a₀).val =
      (⟨(LevelTree.lev (F a₀)-1)+1,
        kptRecordAtLevel ((LevelTree.lev (F a₀)-1)+1) b hb⟩ :
        RawPartialTypeNode db du dd) := by
    rw [hCross]
    exact kptRecordAtLevel_raw
      ((LevelTree.lev (F a₀)-1)+1) b hb
  exact genuine_gap_boundary_one_target_B3
    family F q₀ a₀ hprev hgap
    (kptRecordAtLevel ((LevelTree.lev (F a₀)-1)+1) b hb)
    hImage

end Kk
