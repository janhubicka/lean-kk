import Kk.FullPhysicalCrossingRelation
import Mathlib.Tactic

/-!
# Track E: compare distinct physical closures by their complete crossing relation

No literal equality of the two Kpt closure sets is required. At one
ALIGNED source cut, equality of the canonical full old+upper L+ crossing
relations identifies the two prescribed full source/target graphs and
the corrected B3 verdict, provided BOTH stages have actual Cover and
Graph certificates. The final theorem specializes this to two genuine
finite numerical H+ stages with potentially different ambient sizes.

This does NOT establish such equality from an unrefined KK macrodiary;
the synchronized full microevent/parameter-closed source comparison
remains the mathematical critical path.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Equality of the **source graphs** of two partial prescribed maps
identifies their source domains and COMPLETE assigned upper L+ values.
No equality of arbitrary F.target values outside F.source is inferred. -/
theorem full_prescribed_graph_eq_implies_source_and_target_eq
    {db du dd cut : Nat}
    (F G : PrescribedBoringData cut db du dd)
    (hGraph : fullPrescribedCrossingGraph F =
      fullPrescribedCrossingGraph G) :
    F.source = G.source ∧
      ∀ T, T ∈ F.source → F.target T = G.target T := by
  have hFG : ∀ T, T ∈ F.source →
      T ∈ G.source ∧ F.target T = G.target T := by
    intro T hT
    have hPair : (T,F.target T) ∈ fullPrescribedCrossingGraph G := by
      rw [← hGraph]
      exact ⟨hT,rfl⟩
    change T ∈ G.source ∧ G.target T = F.target T at hPair
    exact ⟨hPair.1,hPair.2.symm⟩
  have hGF : ∀ T, T ∈ G.source → T ∈ F.source := by
    intro T hT
    have hPair : (T,G.target T) ∈ fullPrescribedCrossingGraph F := by
      rw [hGraph]
      exact ⟨hT,rfl⟩
    change T ∈ F.source ∧ F.target T = G.target T at hPair
    exact hPair.1
  constructor
  · ext T
    constructor
    · intro hT
      exact (hFG T hT).1
    · intro hT
      exact hGF T hT
  · intro T hT
    exact (hFG T hT).2

/-- TWO genuinely different physical Kpt closures with the same
full crossing relation at one aligned source cut have identical
complete prescribed old/upper source graph and corrected B3 verdict,
if their chosen prescribed maps cover ALL and ONLY those crossings.

Neither an equality of the whole closure sets nor equality of their
chosen original-name pools is needed; the remaining assumption is
literal equality of complete physical old+upper L+ crossing RELATIONS. -/
theorem two_closures_full_crossings_and_B3_of_equal_physical_relation
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (cut : Nat)
    (F G : PrescribedBoringData cut db du dd)
    (hCoverF : CoversClosureCrossing family Z₁ cut F)
    (hGraphF : IsCrossingGraphOf family Z₁ cut F)
    (hCoverG : CoversClosureCrossing family Z₂ cut G)
    (hGraphG : IsCrossingGraphOf family Z₂ cut G)
    (hPhysical :
      FullPhysicalClosureCrossing family Z₁ cut =
        FullPhysicalClosureCrossing family Z₂ cut) :
    F.source = G.source ∧
      (∀ T, T ∈ F.source → F.target T = G.target T) ∧
      (F.CorrectedB3 family ↔ G.CorrectedB3 family) := by
  have hPrescribed :
      fullPrescribedCrossingGraph F =
        fullPrescribedCrossingGraph G := by
    calc
      fullPrescribedCrossingGraph F =
          FullPhysicalClosureCrossing family Z₁ cut :=
        prescribed_full_graph_eq_physical_crossing
          family Z₁ cut F hCoverF hGraphF
      _ = FullPhysicalClosureCrossing family Z₂ cut := hPhysical
      _ = fullPrescribedCrossingGraph G :=
        (prescribed_full_graph_eq_physical_crossing
          family Z₂ cut G hCoverG hGraphG).symm
  obtain ⟨hSource,hTargets⟩ :=
    full_prescribed_graph_eq_implies_source_and_target_eq F G hPrescribed
  exact ⟨hSource,hTargets,
    correctedB3_iff_of_identical_full_crossing_graph
      family F G hSource hTargets⟩

/-- A physical CROSS-PRESENTATION Track E interface: two actual finite
numerical H+ structures (possibly different graph models, heights,
source-name cardinalities and finite universes) have the same
complete source graph and corrected B3 verdict at an aligned cut,
provided the complete Kpt crossing RELATIONS match exactly.

Both source pool coverage and absence of I2 competition are supplied
for each individual physical closure by Track C; no equality of the
whole two closures is assumed. The key hPhysical hypothesis is STILL
a missing full microdiary comparison across diary occurrences. -/
theorem two_numericH_closures_B3_of_equal_full_crossing_relation
    {db du dd M₁ M₂ : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K₁ K₂ : AgeTestModel db du dd)
    (k₁ N₁ k₂ N₂ : Nat)
    (hAvoid₁ : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K₁ k₁ N₁).L)
    (hAvoid₂ : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K₂ k₂ N₂).L)
    (original₁ : Fin M₁ → Fin (finiteNumericH K₁ k₁ N₁).size)
    (original₂ : Fin M₂ → Fin (finiteNumericH K₂ k₂ N₂).size)
    (Z₁ Z₂ : Set (AdmissibleKptNode family))
    (hPool₁ : ∀ z, z ∈ Z₁ →
      ∃ v : Fin M₁,
        z ≤ (finiteNumericH K₁ k₁ N₁).kptOriginal family hAvoid₁ (original₁ v))
    (hPool₂ : ∀ z, z ∈ Z₂ →
      ∃ v : Fin M₂,
        z ≤ (finiteNumericH K₂ k₂ N₂).kptOriginal family hAvoid₂ (original₂ v))
    (cut : Nat)
    (hNoMeet₁ : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z₁ ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z₁ ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hNoMeet₂ : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z₂ ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z₂ ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hPhysical :
      FullPhysicalClosureCrossing family Z₁ cut =
        FullPhysicalClosureCrossing family Z₂ cut) :
    let F : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K₁ k₁ N₁) hAvoid₁ original₁ Z₁ cut
    let G : PrescribedBoringData cut db du dd :=
      closureSelectedBoringData family
        (finiteNumericH K₂ k₂ N₂) hAvoid₂ original₂ Z₂ cut
    F.source = G.source ∧
      (∀ T, T ∈ F.source → F.target T = G.target T) ∧
      (F.CorrectedB3 family ↔ G.CorrectedB3 family) := by
  let F : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family
      (finiteNumericH K₁ k₁ N₁) hAvoid₁ original₁ Z₁ cut
  let G : PrescribedBoringData cut db du dd :=
    closureSelectedBoringData family
      (finiteNumericH K₂ k₂ N₂) hAvoid₂ original₂ Z₂ cut
  obtain ⟨hCoverF,hGraphF,_⟩ :=
    finiteNumericH_named_pool_cut_crossing_and_upper_types
      family K₁ k₁ N₁ hAvoid₁ original₁ Z₁ hPool₁ cut hNoMeet₁
  obtain ⟨hCoverG,hGraphG,_⟩ :=
    finiteNumericH_named_pool_cut_crossing_and_upper_types
      family K₂ k₂ N₂ hAvoid₂ original₂ Z₂ hPool₂ cut hNoMeet₂
  exact two_closures_full_crossings_and_B3_of_equal_physical_relation
    family Z₁ Z₂ cut F G
    hCoverF hGraphF hCoverG hGraphG hPhysical

end Kk
