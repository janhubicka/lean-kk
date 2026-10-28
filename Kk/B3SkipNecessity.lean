import Kk.B3ReductProfile
import SuccessorTree.V10.M2BoundaryCompatibleB3Closure
import Mathlib.Tactic

/-!
# A necessary corrected-B3 age test for genuine one-gap Kpt maps

The successor library already proves that every genuine Kpt ShapeMap
with a source-level image gap has corrected CompatibleB3 for its
ACTUAL boundary family of complete L+ records. Separately,
Kk.B3ReductProfile proves that a smaller L-only age profile inherits
corrected B3 when its socles and complete upper types are covered.

These two checked statements combine to produce an exact
*necessary* criterion for skipping a numerical cut: any marked
source/target subprofile of one compatibility class of the true
shape-map boundary must itself pass corrected B3.

This offers the missing reverse direction for attempts to turn a
finite Henson B3 witness into an Algorithm 5.4 interesting level.
It does not assert that an arbitrary candidate matched diary
profile actually agrees with the shape-map boundary. For the
K4 first-gadget cuts 10 and 22, that identification remains the
nontrivial application obligation.

No new axiom, E structure on age-test continuations, or generic
B3-to-I3 equivalence is assumed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Any true Kpt shape map with a first consecutive source-level gap
has a corrected-B3-admissible boundary after restriction to each
actual ordinary-L+ compatibility class.

This is a necessity theorem about the ACTUAL image records of F,
not about a freely prescribed candidate profile. -/
theorem kpt_gap_boundary_class_correctedB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
    (hS0 :
      S0 ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source) :
    ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
      .restrictToCompatible S0).CorrectedB3 family := by
  let P : PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd :=
    m2Boundary_prescribedData family F q₀ a₀ hprev hgap
  have hCompatible : P.CompatibleB3 family :=
    m2Boundary_actual_compatibleB3 family F q₀ a₀ hprev hgap
  exact (P.compatibleB3_iff_restricted_correctedB3 family).1
    hCompatible S0 hS0

/-- A marked local profile dominated by one actual Kpt shape-map
boundary class necessarily passes corrected B3.

If a numerical H gadget produces a forbidden-clique B3 witness for
the marked profile, then the claimed shape-map skip cannot exist
*provided* these two exact L-reduct dominance hypotheses hold. -/
theorem correctedB3_of_genuine_kpt_gap_Lprofile
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
    (hS0 :
      S0 ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source)
    (marked : PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd)
    (hSocle : ∀ S, S ∈ marked.source →
      ∃ T, T ∈ ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
        .restrictToCompatible S0).source ∧
        SameInitialL
          (prescribedOrdinarySocle (marked.target S))
          (prescribedOrdinarySocle
            (((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
                .restrictToCompatible S0).target T))
          (LevelTree.lev (F a₀)-1))
    (hUpper : ∀ R, marked.PrescribedUpperLType R →
      ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
        .restrictToCompatible S0).PrescribedUpperLType R) :
    marked.CorrectedB3 family := by
  exact correctedB3_of_Lprofile_dominance
    marked
    ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
      .restrictToCompatible S0)
    family hSocle hUpper
    (kpt_gap_boundary_class_correctedB3 family F q₀ a₀
      hprev hgap S0 hS0)

/-- Concrete source/subprofile formulation: the marked complete
source types form a subset of an actual boundary compatibility
class and their prescribed complete next types are identical
to the genuine boundary targets. These are sufficient to use
the shape-map necessity theorem with no separately assumed
age-spectrum relation. -/
theorem correctedB3_of_genuine_kpt_gap_subprofile
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
    (hS0 :
      S0 ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source)
    (marked : PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd)
    (hSource : ∀ T, T ∈ marked.source →
      T ∈ ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
        .restrictToCompatible S0).source)
    (hTarget : ∀ T, T ∈ marked.source →
      marked.target T =
        ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
          .restrictToCompatible S0).target T) :
    marked.CorrectedB3 family := by
  apply correctedB3_of_genuine_kpt_gap_Lprofile
    family F q₀ a₀ hprev hgap S0 hS0 marked
  · intro S hS
    refine ⟨S,hSource S hS,?_⟩
    rw [hTarget S hS]
    exact ⟨by intros; rfl, by intros; rfl,
      by intros; rfl, by intros; rfl⟩
  · intro R hR
    obtain ⟨T,hT,hEq⟩ := hR
    refine ⟨T,hSource T hT,?_⟩
    rw [hTarget T hT] at hEq
    exact hEq

end Kk
