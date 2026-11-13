import Kk.NumericHFinalPoolCrossing
import Kk.B3ReductProfile
import Mathlib.Tactic

/-!
# Track E: pool-independent full Kpt closure crossing

English proof and hostile audit:
  docs/track_e_pool_independence_english_audit.md

This proves a genuinely geometric, one-closure uniqueness result:
when two actual prescribed maps both COVER all and ONLY the consecutive
crossings of the same complete Kpt closure, their full source/upper-L+
graphs agree. Track C supplies the two required cover/graph certificates
from two possibly unrelated finite numerical-H original-name pools, if
both represent the SAME physical closure and there is no (I2) meet.

No cross-occurrence diary normalization is assumed or concluded.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One-sided source/target inclusion: every graph edge of F is
represented by a real closure crossing, so completeness of G forces
the same old type and the SAME entire upper L+ successor type. -/
theorem closure_crossing_source_target_le_of_cover_graph
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (F G : PrescribedBoringData cut db du dd)
    (hGraphF : IsCrossingGraphOf family Z cut F)
    (hCoverG : CoversClosureCrossing family Z cut G) :
    ∀ T, T ∈ F.source →
      T ∈ G.source ∧ F.target T = G.target T := by
  intro T hT
  obtain ⟨z,hZ,hCut,hOldF,hUpperF⟩ := hGraphF T hT
  obtain ⟨U,hU,hOldG,hUpperG⟩ := hCoverG z hZ hCut
  have hOldPair :
      (⟨cut,T⟩ : RawPartialTypeNode db du dd) =
      (⟨cut,U⟩ : RawPartialTypeNode db du dd) :=
    hOldF.trans hOldG.symm
  have hTU : T = U := eq_of_heq (Sigma.mk.inj_iff.mp hOldPair).2
  have hUpperPair :
      (⟨cut+1,F.target T⟩ : RawPartialTypeNode db du dd) =
      (⟨cut+1,G.target U⟩ : RawPartialTypeNode db du dd) :=
    hUpperF.trans hUpperG.symm
  have hUpperEq : F.target T = G.target U :=
    eq_of_heq (Sigma.mk.inj_iff.mp hUpperPair).2
  constructor
  · simpa only [← hTU] using hU
  · exact hUpperEq.trans (congrArg G.target hTU.symm)

/-- A full-closure crossing has a unique complete L+ source-to-upper
graph; neither finite ambient original names nor target-choice
witnesses enter the conclusion. Cover and Graph are needed for BOTH
maps. The closure Z is literally the SAME set of actual Kpt nodes. -/
theorem closure_crossing_graph_unique_of_two_sided_coverage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (cut : Nat)
    (F G : PrescribedBoringData cut db du dd)
    (hCoverF : CoversClosureCrossing family Z cut F)
    (hGraphF : IsCrossingGraphOf family Z cut F)
    (hCoverG : CoversClosureCrossing family Z cut G)
    (hGraphG : IsCrossingGraphOf family Z cut G) :
    F.source = G.source ∧
      ∀ T, T ∈ F.source → F.target T = G.target T := by
  have hFG :=
    closure_crossing_source_target_le_of_cover_graph
      family Z cut F G hGraphF hCoverG
  have hGF :=
    closure_crossing_source_target_le_of_cover_graph
      family Z cut G F hGraphG hCoverF
  constructor
  · ext T
    constructor
    · intro hT
      exact (hFG T hT).1
    · intro hT
      exact (hGF T hT).1
  · intro T hT
    exact (hFG T hT).2

/-- A PHYSICAL finite numerical H+ application.
For two arbitrary finite original-name pools of different sizes,
both covering the SAME complete physical closure Z, the
canonical closure-selected prescribed maps agree on their whole
source, including ALL L+ upper types and auxiliary E, whenever no
(I2) meet competes at the tested cut.

This removes arbitrary pool-choice dependence from the local Track E
record, but it does not compare *different occurrences* / closures. -/
theorem finiteNumericH_full_crossing_independent_of_original_pool
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (original₁ : Fin M₁ → Fin (finiteNumericH K k N).size)
    (original₂ : Fin M₂ → Fin (finiteNumericH K k N).size)
    (Z : Set (AdmissibleKptNode family))
    (hPool₁ : ∀ z, z ∈ Z →
      ∃ v : Fin M₁,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original₁ v))
    (hPool₂ : ∀ z, z ∈ Z →
      ∃ v : Fin M₂,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original₂ v))
    (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original₁ Z cut
    let G : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original₂ Z cut
    F.source = G.source ∧
      ∀ T, T ∈ F.source → F.target T = G.target T := by
  obtain ⟨hCoverF,hGraphF,_⟩ :=
    finiteNumericH_named_pool_cut_crossing_and_upper_types
      family K k N hAvoid original₁ Z hPool₁ cut hNoMeet
  obtain ⟨hCoverG,hGraphG,_⟩ :=
    finiteNumericH_named_pool_cut_crossing_and_upper_types
      family K k N hAvoid original₂ Z hPool₂ cut hNoMeet
  exact closure_crossing_graph_unique_of_two_sided_coverage
    family Z cut
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original₁ Z cut)
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original₂ Z cut)
    hCoverF hGraphF hCoverG hGraphG


/-- Equal **full L+ crossing graphs** induce identical corrected (B3)
finite L-age verdicts. The age-test continuations are still ordinary
L structures; no auxiliary E is assigned to these arbitrary witnesses.
This theorem requires no finite original-name pool, only exact equality
of source domains and complete next types on that domain. -/
theorem correctedB3_iff_of_identical_full_crossing_graph
    {db du dd cut : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F G : PrescribedBoringData cut db du dd)
    (hSource : F.source = G.source)
    (hTarget : ∀ T, T ∈ F.source → F.target T = G.target T) :
    F.CorrectedB3 family ↔ G.CorrectedB3 family := by
  have hUpper : F.PrescribedUpperLType = G.PrescribedUpperLType := by
    funext R
    apply propext
    constructor
    · rintro ⟨T,hTF,hR⟩
      have hTG : T ∈ G.source := by rw [← hSource]; exact hTF
      refine ⟨T,hTG,?_⟩
      calc
        R = (F.target T).lReduct := hR
        _ = (G.target T).lReduct :=
          congrArg
            (fun Q : PartialTypeWithE (cut+1) db du dd => Q.lReduct)
            (hTarget T hTF)
    · rintro ⟨T,hTG,hR⟩
      have hTF : T ∈ F.source := by rw [hSource]; exact hTG
      refine ⟨T,hTF,?_⟩
      calc
        R = (G.target T).lReduct := hR
        _ = (F.target T).lReduct :=
          congrArg
            (fun Q : PartialTypeWithE (cut+1) db du dd => Q.lReduct)
            (hTarget T hTF).symm
  constructor
  · intro hF T hTG
    have hTF : T ∈ F.source := by rw [hSource]; exact hTG
    have h := hF T hTF
    change CommonSocleAgeTest family
      (prescribedOrdinarySocle (G.target T)) cut
      G.PrescribedUpperLType
    rw [← hTarget T hTF, ← hUpper]
    exact h
  · intro hG T hTF
    have hTG : T ∈ G.source := by rw [← hSource]; exact hTF
    have h := hG T hTG
    change CommonSocleAgeTest family
      (prescribedOrdinarySocle (F.target T)) cut
      F.PrescribedUpperLType
    rw [hTarget T hTF, hUpper]
    exact h

/-- The actual finite numerical H+ corrected-(B3) verdict at a cut
depends on the COMPLETE closure, not on the chosen exhaustive finite
original-name pool representing that closure. The proof compares the
genuine full L+ source graphs first and then applies the exact
source/upper-graph B3 extensionality theorem. -/
theorem finiteNumericH_correctedB3_independent_of_original_pool
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (original₁ : Fin M₁ → Fin (finiteNumericH K k N).size)
    (original₂ : Fin M₂ → Fin (finiteNumericH K k N).size)
    (Z : Set (AdmissibleKptNode family))
    (hPool₁ : ∀ z, z ∈ Z →
      ∃ v : Fin M₁,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original₁ v))
    (hPool₂ : ∀ z, z ∈ Z →
      ∃ v : Fin M₂,
        z ≤ (finiteNumericH K k N).kptOriginal family hAvoid (original₂ v))
    (cut : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original₁ Z cut
    let G : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family A hAvoid original₂ Z cut
    F.CorrectedB3 family ↔ G.CorrectedB3 family := by
  obtain ⟨hSource,hTarget⟩ :=
    finiteNumericH_full_crossing_independent_of_original_pool
      family K k N hAvoid original₁ original₂ Z
      hPool₁ hPool₂ cut hNoMeet
  exact correctedB3_iff_of_identical_full_crossing_graph family
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original₁ Z cut)
    (closureSelectedBoringData family (finiteNumericH K k N)
      hAvoid original₂ Z cut)
    hSource hTarget

end Kk
