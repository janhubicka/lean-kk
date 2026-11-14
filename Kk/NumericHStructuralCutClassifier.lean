import Kk.NumericHPhysicalI2Fork
import Mathlib.Tactic

/-!
# Track C: unconditional full-source I1/I2 structural cut classifier

English proof and hostile audit committed FIRST:
  docs/track_c_structural_cut_classifier_english_audit.md

The exact structural alternative is NOT "I2 iff a fork" at an
arbitrary cut: an (I1) node at the cut gives a trivial self-meet
without crossing. The valid unconditional statement is

  (I1 OR I2) iff (I1 OR full L+ fork).

The same dichotomy is expressed using either the choice-free
FullPhysicalClosureCrossing relation or the one true finite
AlgorithmRun's COMPLETE active Kpt source-node index. False
atoms and auxiliary E remain part of every raw old/upper type.

No assertion about actual I3 or corrected B3, resolved-copy
recursion, cross-occurrence coherence or Ramsey-degree optimality.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Exact structural I1 predicate for the FULL Kpt closure Z. -/
def KptI1AtCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) : Prop :=
  ∃ z : AdmissibleKptNode family, z ∈ Z ∧ LevelTree.lev z = cut

/-- Literal competing I2 meet predicate on the FULL Kpt closure Z.
It may include trivial meets of I1-level nodes, so the genuine
AlgorithmRun trichotomy must give I1 priority. -/
def KptI2MeetAtCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) : Prop :=
  ∃ a : AdmissibleKptNode family, a ∈ Z ∧
    ∃ b : AdmissibleKptNode family, b ∈ Z ∧
      SMTree.Envelope.SameComponent a b ∧
      LevelTree.lev (LevelTree.meet a b) = cut

/-- UNCONDITIONAL structural alternative: a true I1-or-I2
event is precisely either a present node at the cut or a
nonfunctional full-dependent-L+ fork. No no-I1 assumption. -/
theorem kpt_I1_or_I2_iff_I1_or_complete_full_fork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) :
    (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
      (KptI1AtCut family Z cut ∨ KptFullCutFork family Z cut) := by
  constructor
  · intro h
    rcases h with hI1 | hI2
    · exact Or.inl hI1
    · exact kpt_I2_meet_implies_I1_or_full_fork
        family Z cut hI2
  · intro h
    rcases h with hI1 | hFork
    · exact Or.inl hI1
    · exact Or.inr (kpt_full_cut_fork_forces_I2_meet
        family Z cut hFork)

/-- The canonical full physical crossing relation gives EXACTLY
the same unconditional structural alternative. A nonfunctional
physical old/upper L+ relation certifies I2, while a trivial
I1 meet is caught by the explicit I1 disjunct. -/
theorem kpt_I1_or_I2_iff_I1_or_physical_nonfunctional
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family)) (cut : Nat) :
    (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
    (KptI1AtCut family Z cut ∨
      ∃ T : PartialTypeWithE cut db du dd,
        ∃ U V : PartialTypeWithE (cut+1) db du dd,
          (T,U) ∈ FullPhysicalClosureCrossing family Z cut ∧
          (T,V) ∈ FullPhysicalClosureCrossing family Z cut ∧
          U ≠ V) := by
  constructor
  · intro h
    rcases (kpt_I1_or_I2_iff_I1_or_complete_full_fork
      family Z cut).mp h with hI1 | hFork
    · exact Or.inl hI1
    · exact Or.inr
        (kpt_full_fork_forces_physical_crossing_nonfunctional
          family Z cut hFork)
  · intro h
    rcases h with hI1 | hPhysical
    · exact Or.inl hI1
    · obtain ⟨T,U,V,hTU,hTV,hNe⟩ := hPhysical
      exact Or.inr (full_physical_crossing_nonfunctional_forces_I2
        family Z cut T U V hTU hTV hNe)

/-- At one ACTUAL finite numerical H+ AlgorithmRun, the entire
structural I1-or-I2 obstruction is equivalent to a FINITE
ACTIVE-source certificate:
  * one active complete-Kpt node exactly at the cut, OR
  * two active complete-Kpt nodes strictly crossing the cut
    with equal full OLD and distinct full UPPER L+ records.

No no-I1 assumption is required. The finite index includes
every generated parameter/meet node, not a selected shadow.
There is NO claim of an executable closed-form bound on the
size of the index or of synchronization between two runs. -/
theorem finiteNumericH_run_structural_I1I2_iff_active_node_or_fork
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X)
    (cut : Nat) (hCut : cut < top) :
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (cut+1)) X
    (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
    ((∃ i : Fin params.card,
       presentAt cut i = true ∧
       LevelTree.lev (params.equivFin.symm i).val = cut) ∨
      (∃ i j : Fin params.card,
        presentAt cut i = true ∧ presentAt cut j = true ∧
        cut < LevelTree.lev (params.equivFin.symm i).val ∧
        cut < LevelTree.lev (params.equivFin.symm j).val ∧
        kptFullOldAtCut (params.equivFin.symm i).val cut =
          kptFullOldAtCut (params.equivFin.symm j).val cut ∧
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut)) := by
  classical
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X
  have hLevels : R.I (cut+1) ⊆ R.I 0 := by
    intro q hq
    rw [R.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  have hFinal : Z ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I 0) X :=
    envelope_closure_mono_levels
      (admissibleKptSTree family)
      (R.I (cut+1)) (R.I 0) X hLevels
  have hCovered :
      Z ⊆ (params : Set (AdmissibleKptNode family)) := by
    intro z hz
    exact (hParams z).2 (hFinal hz)
  have hI1Index :
      KptI1AtCut family Z cut ↔
        ∃ i : Fin params.card,
          presentAt cut i = true ∧
          LevelTree.lev (params.equivFin.symm i).val = cut := by
    constructor
    · rintro ⟨z,hz,hLev⟩
      have hzParams : z ∈ params := hCovered hz
      let i : Fin params.card := params.equivFin ⟨z,hzParams⟩
      have hNode : (params.equivFin.symm i).val = z := by
        simp [i]
      refine ⟨i, (hPresent cut i).2 ?_, ?_⟩
      · simpa only [hNode] using hz
      · simpa only [hNode] using hLev
    · rintro ⟨i,hLive,hLev⟩
      exact ⟨(params.equivFin.symm i).val,
        (hPresent cut i).1 hLive,hLev⟩
  have hForkIndex :
      KptFullCutFork family Z cut ↔
        ∃ i j : Fin params.card,
          presentAt cut i = true ∧ presentAt cut j = true ∧
          cut < LevelTree.lev (params.equivFin.symm i).val ∧
          cut < LevelTree.lev (params.equivFin.symm j).val ∧
          kptFullOldAtCut (params.equivFin.symm i).val cut =
            kptFullOldAtCut (params.equivFin.symm j).val cut ∧
          kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
            kptFullUpperAtCut (params.equivFin.symm j).val cut :=
    kpt_full_fork_iff_finite_active_indices
      family Z cut params hCovered (presentAt cut) (hPresent cut)
  have hStructure :=
    kpt_I1_or_I2_iff_I1_or_complete_full_fork family Z cut
  change (KptI1AtCut family Z cut ∨ KptI2MeetAtCut family Z cut) ↔
    ((∃ i : Fin params.card,
       presentAt cut i = true ∧
       LevelTree.lev (params.equivFin.symm i).val = cut) ∨
      (∃ i j : Fin params.card,
        presentAt cut i = true ∧ presentAt cut j = true ∧
        cut < LevelTree.lev (params.equivFin.symm i).val ∧
        cut < LevelTree.lev (params.equivFin.symm j).val ∧
        kptFullOldAtCut (params.equivFin.symm i).val cut =
          kptFullOldAtCut (params.equivFin.symm j).val cut ∧
        kptFullUpperAtCut (params.equivFin.symm i).val cut ≠
          kptFullUpperAtCut (params.equivFin.symm j).val cut))
  constructor
  · intro h
    rcases hStructure.mp h with hI1 | hFork
    · exact Or.inl (hI1Index.mp hI1)
    · exact Or.inr (hForkIndex.mp hFork)
  · intro h
    apply hStructure.mpr
    rcases h with hI1 | hFork
    · exact Or.inl (hI1Index.mpr hI1)
    · exact Or.inr (hForkIndex.mpr hFork)

#print axioms Kk.kpt_I1_or_I2_iff_I1_or_complete_full_fork
#print axioms Kk.kpt_I1_or_I2_iff_I1_or_physical_nonfunctional
#print axioms Kk.finiteNumericH_run_structural_I1I2_iff_active_node_or_fork

end Kk
