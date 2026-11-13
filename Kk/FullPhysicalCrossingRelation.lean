import Kk.FullCrossingPoolIndependence
import Mathlib.Tactic

/-!
# Track E: canonical physical full-L+ crossing RELATION

The actual relation of consecutive full Kpt ancestors exists whether
or not (I2) holds. It does not depend on chosen finite original names,
chosen target representatives, or arbitrary total values of a
prescribed function outside its genuine source.

English proof and adversarial audit appear in
docs/track_e_pool_independence_english_audit.md.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Canonical complete physical crossing RELATION of the actual closure
Z at cut. T and U retain the entire partial L+ record including E.
Unlike a prescribed crossing FUNCTION, this relation is meaningful
even at a competing (I2) level. -/
def FullPhysicalClosureCrossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat) :
    Set (PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd) :=
  {p | ∃ z : AdmissibleKptNode family,
    z ∈ Z ∧ ∃ (hz : cut < LevelTree.lev z),
      (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z cut (Nat.le_of_lt hz)).val ∧
      (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hz)).val}

/-- Compare only the GRAPH of a partial prescribed function.
Values of F.target outside F.source are intentionally ignored. -/
def PrescribedBoringData.fullSourceGraph
    {db du dd cut : Nat}
    (F : PrescribedBoringData cut db du dd) :
    Set (PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd) :=
  {p | p.1 ∈ F.source ∧ F.target p.1 = p.2}

/-- A genuine fork in the complete physical crossing relation yields a
REAL competing (I2) meet between two nodes of the same actual closure.

The proof uses the verified "next prefixes coincide without a cut
meet" theorem, contrapositive. It is NOT about a selected-shadow
projection. The reverse implication is deliberately not asserted. -/
theorem full_physical_crossing_nonfunctional_forces_I2
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (T : PartialTypeWithE cut db du dd)
    (U V : PartialTypeWithE (cut+1) db du dd)
    (hU : (T,U) ∈ FullPhysicalClosureCrossing family Z cut)
    (hV : (T,V) ∈ FullPhysicalClosureCrossing family Z cut)
    (hNe : U ≠ V) :
    ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut := by
  obtain ⟨z,hz,hCutZ,hOldZ,hUpperZ⟩ := hU
  obtain ⟨w,hw,hCutW,hOldW,hUpperW⟩ := hV
  have hOldEq :
      LevelTree.ancestor z cut (Nat.le_of_lt hCutZ) =
        LevelTree.ancestor w cut (Nat.le_of_lt hCutW) := by
    apply Subtype.ext
    exact hOldZ.symm.trans hOldW
  have hCommon : SMTree.Envelope.SameComponent z w := by
    refine ⟨LevelTree.ancestor z cut (Nat.le_of_lt hCutZ),
      LevelTree.ancestor_le z cut (Nat.le_of_lt hCutZ),?_⟩
    rw [hOldEq]
    exact LevelTree.ancestor_le w cut (Nat.le_of_lt hCutW)
  have hNextNe :
      LevelTree.ancestor z (cut+1) (Nat.succ_le_iff.mpr hCutZ) ≠
        LevelTree.ancestor w (cut+1) (Nat.succ_le_iff.mpr hCutW) := by
    intro hEq
    have hRaw :
        (⟨cut+1,U⟩ : RawPartialTypeNode db du dd) =
          (⟨cut+1,V⟩ : RawPartialTypeNode db du dd) :=
      hUpperZ.trans (congrArg Subtype.val hEq).trans hUpperW.symm
    exact hNe (eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2)
  have hMeetLevel : LevelTree.lev (LevelTree.meet z w) = cut := by
    by_contra hNot
    exact hNextNe
      (SMTree.Envelope.nextPrefix_eq_of_no_meet
        hCutZ hCutW hOldEq hNot)
  exact ⟨z,hz,w,hw,hCommon,hMeetLevel⟩

/-- If no genuine (I2) meet exists, every actual old full L+ source
record has at most one complete upper record. This is the precise
functionality part of the canonical physical crossing relation. -/
theorem full_physical_crossing_functional_of_no_I2
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b : AdmissibleKptNode family, b ∈ Z ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    ∀ T U V,
      (T,U) ∈ FullPhysicalClosureCrossing family Z cut →
      (T,V) ∈ FullPhysicalClosureCrossing family Z cut →
      U = V := by
  intro T U V hU hV
  by_contra hNe
  exact hNoMeet
    (full_physical_crossing_nonfunctional_forces_I2
      family Z cut T U V hU hV hNe)

/-- A prescribed map that contains ALL and ONLY actual crossings has
a source graph which is LITERALLY the canonical physical relation.
No change of finite original names can alter it. Both directions are
necessary to exclude missing and extraneous crossings. -/
theorem prescribed_full_graph_eq_physical_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (F : PrescribedBoringData cut db du dd)
    (hCover : CoversClosureCrossing family Z cut F)
    (hGraph : IsCrossingGraphOf family Z cut F) :
    F.fullSourceGraph = FullPhysicalClosureCrossing family Z cut := by
  ext p
  constructor
  · rintro ⟨hSource,hTarget⟩
    obtain ⟨z,hZ,hCut,hOld,hNext⟩ := hGraph p.1 hSource
    refine ⟨z,hZ,hCut,hOld,?_⟩
    simpa only [← hTarget] using hNext
  · rintro ⟨z,hZ,hCut,hOld,hNext⟩
    obtain ⟨T,hT,hOldF,hNextF⟩ := hCover z hZ hCut
    have hOldEq :
        (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
          (⟨cut,T⟩ : RawPartialTypeNode db du dd) :=
      hOld.trans hOldF.symm
    have hpT : p.1 = T := eq_of_heq (Sigma.mk.inj_iff.mp hOldEq).2
    have hNextEq :
        (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
          (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd) :=
      hNext.trans hNextF.symm
    have hpNext : p.2 = F.target T :=
      eq_of_heq (Sigma.mk.inj_iff.mp hNextEq).2
    constructor
    · rw [hpT]
      exact hT
    · rw [hpT]
      exact hpNext.symm

/-- Track C physically discharges both cover and graph conditions for
the exact numerical-H+ closure-selected prescribed map at a no-I2 cut.
Consequently the chosen source/upper-L+ map's graph is exactly the
canonical, choice-free physical closure crossing relation. -/
theorem finiteNumericH_full_crossing_graph_is_physical_relation
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (original : Fin M → Fin (finiteNumericH K k N).size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original v))
    (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original Z cut).fullSourceGraph =
        FullPhysicalClosureCrossing family Z cut := by
  obtain ⟨hCover,hGraph,_⟩ :=
    finiteNumericH_named_pool_cut_crossing_and_upper_types
      family K k N hAvoid original Z hPool cut hNoMeet
  exact prescribed_full_graph_eq_physical_crossing
    family Z cut
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original Z cut)
    hCover hGraph

end Kk
