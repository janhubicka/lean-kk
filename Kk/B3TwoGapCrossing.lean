import Kk.B3SkipNecessity
import SuccessorTree.V10.M2BoundaryCompatibleB3Closure
import Mathlib.Tactic

/-!
# Two genuine crossed Kpt upper L-types also obey corrected B3

The earlier one-crossing necessity theorem suffices for the K4
second gadget cut (two copies of x). At the FIRST gadget cut, a
genuine forbidden continuation instead uses one copy of an
auxiliary q2 upper type and two copies of the active x upper type.

Here we isolate the exact necessary age condition for any genuine
one-gap Kpt shape map: choose two actual boundary source nodes
at the same source level whose *deleted* complete L+ records
have the same ordinary socle. Any finite continuation using just
their two FULL output L-reduct types must pass corrected B3.

This follows from the already proved M2 boundary CompatibleB3
theorem, with actual indexed source/target equalities.
It does NOT assume that two arbitrary chosen marked profiles
come from the same source, or that the auxiliary q2 lies in the
Algorithm 5.4 closure. Those concrete identifications remain
separate K4 application obligations.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuine Kpt one-gap boundary satisfies finite L-only B3
for any two *compatible* actual boundary source indices.

The conclusion retains both full prescribed L-types and
allows arbitrary combinations and repetitions of them among
future age-test vertices. In particular, it does NOT freeze
future--future L edges to the real ambient H graph. -/
theorem genuine_gap_boundary_two_targets_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (a₁ : AdmissibleKptNode family)
    (ha₁ : LevelTree.lev a₁ = LevelTree.lev a₀)
    (hComp : SameOrdinaryAtCut
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap
        (⟨a₁,ha₁⟩ : M2BoundaryIndex family a₀))
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap
        (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀))) :
    CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀)))
      (LevelTree.lev (F a₀)-1)
      (fun R =>
        R = (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀)).lReduct ∨
        R = (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₁,ha₁⟩ : M2BoundaryIndex family a₀)).lReduct) := by
  let i₀ : M2BoundaryIndex family a₀ := ⟨a₀,rfl⟩
  let i₁ : M2BoundaryIndex family a₀ := ⟨a₁,ha₁⟩
  let P : PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd :=
    m2Boundary_prescribedData family F q₀ a₀ hprev hgap
  let S₀ := m2Boundary_sourceType family F q₀ a₀ hprev hgap i₀
  let S₁ := m2Boundary_sourceType family F q₀ a₀ hprev hgap i₁
  have hSrc₀ : S₀ ∈ P.source :=
    m2Boundary_prescribed_source family F q₀ a₀ hprev hgap i₀
  have hSrc₁ : S₁ ∈ P.source :=
    m2Boundary_prescribed_source family F q₀ a₀ hprev hgap i₁
  have hTarget₀ :
      P.target S₀ = m2Boundary_targetType family F q₀ a₀ hprev hgap i₀ :=
    m2Boundary_prescribed_target family F q₀ a₀ hprev hgap i₀
  have hTarget₁ :
      P.target S₁ = m2Boundary_targetType family F q₀ a₀ hprev hgap i₁ :=
    m2Boundary_prescribed_target family F q₀ a₀ hprev hgap i₁
  have hB3 : P.CompatibleB3 family :=
    m2Boundary_actual_compatibleB3 family F q₀ a₀ hprev hgap
  intro W hFinite hSame hUpper hDelete bad hBad
  have hSameP :
      SameInitialL W
        (prescribedOrdinarySocle (P.target S₀))
        (LevelTree.lev (F a₀)-1) := by
    rw [hTarget₀]
    exact hSame
  have hUpperP :
      UpperTypesPrescribed W (LevelTree.lev (F a₀)-1)
        (P.CompatibleUpperLType S₀) := by
    intro x hx hAbove
    rcases hUpper x hx hAbove with h₀ | h₁
    · refine ⟨S₀,hSrc₀,sameOrdinaryAtCut_refl S₀,?_⟩
      rw [hTarget₀]
      exact h₀
    · refine ⟨S₁,hSrc₁,hComp,?_⟩
      rw [hTarget₁]
      exact h₁
  exact hB3 S₀ hSrc₀ W hFinite hSameP hUpperP hDelete bad hBad

/-- Contrapositive: any finite forbidden continuation using
two compatible actual target L-types forbids the corresponding
genuine Kpt shape-map gap. The required *source compatibility*
is an explicit hypothesis, not an inferred selected shadow. -/
theorem bad_two_upper_precludes_genuine_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (a₁ : AdmissibleKptNode family)
    (ha₁ : LevelTree.lev a₁ = LevelTree.lev a₀)
    (hComp : SameOrdinaryAtCut
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap
        (⟨a₁,ha₁⟩ : M2BoundaryIndex family a₀))
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap
        (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀)))
    (hFailed : ¬ CommonSocleAgeTest family
      (prescribedOrdinarySocle
        (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀)))
      (LevelTree.lev (F a₀)-1)
      (fun R =>
        R = (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₀,rfl⟩ : M2BoundaryIndex family a₀)).lReduct ∨
        R = (m2Boundary_targetType family F q₀ a₀ hprev hgap
          (⟨a₁,ha₁⟩ : M2BoundaryIndex family a₀)).lReduct)) :
    False :=
  hFailed (genuine_gap_boundary_two_targets_B3
    family F q₀ a₀ hprev hgap a₁ ha₁ hComp)

end Kk
