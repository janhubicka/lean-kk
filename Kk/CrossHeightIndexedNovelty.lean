import Kk.CrossHeightNewRootNovelty
import Kk.NewRootIndexedNovelty
import Mathlib.Tactic

/-!
# Track E: finite physical Kpt witnesses for EXTRA cuts under higher tops

The old and new runs may have DIFFERENT scan tops; a REAL old top
seed and seed inclusion guarantee the old selected-levels persist.
A new interesting cut STRICTLY below oldTop then has a genuinely
new live terminal Kpt source node or complete raw old/upper L+
crossing pair. Track C's exhaustive physical source index turns
this into ONE finite active name, with both full type records from
the SAME actual Kpt node.

No B3 converse or macrodiary-inferred source correspondence.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

theorem crossheight_new_selected_Kpt_cut_has_indexed_physical_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y) (oldTop newTop cut : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (hCut : cut < oldTop)
    (hNew : cut ∈ RunY.I cut)
    (hOld : cut ∉ RunX.I cut)
    {Params : Type}
    (node : Params → AdmissibleKptNode family)
    (live : Nat → Params → Bool)
    (hExact : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (RunY.I (cut+1)) Y ↔
      ∃ j : Params, node j = z ∧ live cut j = true) :
    IndexedNewSourceCutWitness family node live
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunX.I (cut+1)) X) cut := by
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  have hNovel :=
    crossheight_new_selected_Kpt_cut_has_new_terminal_or_full_crossing
      family X Y hXY oldTop newTop cut hTopLe hTopSeed
      RunX RunY hCut hNew hOld
  change (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) at hNovel
  rcases hNovel with ⟨z,hZ,hAbsent,hLevel⟩ | ⟨p,hNewPair,hAbsent⟩
  · obtain ⟨j,hNode,hLive⟩ := (hExact z).mp hZ
    left
    refine ⟨j,hLive,?_,?_⟩
    · simpa only [hNode] using hAbsent
    · simpa only [hNode] using hLevel
  · have hSourceEq :=
      indexed_physical_crossing_eq_full_closure_relation
        family node live ZY cut hExact
    have hPairIndexed :
        p ∈ IndexedPhysicalCrossing family node live cut := by
      rw [hSourceEq]
      exact hNewPair
    obtain ⟨j,hLive,hOldRaw,hUpperRaw⟩ := hPairIndexed
    right
    exact ⟨j,hLive,p.1,p.2,hOldRaw,hUpperRaw,hAbsent⟩


theorem finiteNumericH_crossheight_extra_cut_has_finite_source_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (originalPool : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid originalPool)
    (oldTop newTop cut : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (hCut : cut < oldTop)
    (hNew : cut ∈ RunY.I cut)
    (hOld : cut ∉ RunX.I cut) :
    ∃ params : Finset (AdmissibleKptNode family),
      ∃ live : Nat → Fin params.card → Bool,
        (∀ z : AdmissibleKptNode family,
          z ∈ params ↔
          z ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (RunY.I 0) Y) ∧
        IndexedNewSourceCutWitness family
          (fun j : Fin params.card =>
            (params.equivFin.symm j).val)
          live
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RunX.I (cut+1)) X) cut := by
  classical
  obtain ⟨params,live,hParams,_hInjective,_hPresent,hCover⟩ :=
    finiteNumericH_actualRun_uniform_exhaustive_source_index
      family K k N hAvoid originalPool Y hY newTop RunY
  refine ⟨params,live,hParams,?_⟩
  exact crossheight_new_selected_Kpt_cut_has_indexed_physical_witness
    family X Y hXY oldTop newTop cut hTopLe hTopSeed
    RunX RunY hCut hNew hOld
    (fun j : Fin params.card => (params.equivFin.symm j).val)
    live (hCover cut (lt_of_lt_of_le hCut hTopLe))


end Kk
