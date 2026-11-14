import Kk.NumericHNewRootClosureAbsorption
import Kk.ActualRunSeedMonotonicity
import Kk.NewSourceEventWitness
import SuccessorTree.EnvelopeRunExistence
import Mathlib.Tactic

/-!
# Track E: source-exact new-root absorption using genuine run monotonicity

Track C proved that a corrected actual new-root seed
  Y = closure_I X ∪ O
has the SAME full pre-cut closure as bare X∪O at any stage J⊇I.
Its real numerical-H+ lemma assumed the *NEW* run retains the old
selected levels I among its higher levels.

Track E's already kernel-verified actual AlgorithmRun seed-growth
monotonicity DISCHARGES that missing assumption whenever the
inherited generating levels I were selected HIGHER in an actual
OLD run, and both runs have a common source-level top.

No corrected B3 test, no no-I2 condition, and no shadow-only
age equality are introduced. Genuine Kpt old/upper L+ records,
dependent parameter nodes and all auxiliary E bits are literal.

We also construct a canonical new run at an old actual higher-level
cut, and prove that every newly selected level's terminal/crossing
witness comes from the BARE old+new ORIGINAL Kpt sources, not from
the redundant preinsertion of old parameter closure.

English-first proof and hostile audit:
  docs/track_e_new_root_monotone_absorption_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

universe u v

/-- In any genuine (S,M)-tree, TWO actual same-top AlgorithmRuns on
X and Y=closure_I X ∪ O satisfy the exact new-run pre-cut
closure-absorption equation whenever I was already among the OLD
run's higher selected levels.

There is NO hypothesis that the new run keeps I: it follows from
the kernel-checked semantic interestingness and selected-level
monotonicity under genuine seed inclusion X⊆Y.

This is the exact missing premise of Track C's physical new-root
absorption theorem, without assuming a false union distributivity. -/
theorem actual_two_run_preCut_absorption_of_old_higher_levels
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label) (H : SMTree S)
    (X O : Set T) (I : Set Nat)
    (top cut : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun H X top)
    (RunNew : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S I X ∪ O) top)
    (hCut : cut < top)
    (hOldHigher : I ⊆ RunOld.I (cut+1)) :
    SMTree.Envelope.closure S (RunNew.I (cut+1))
      (SMTree.Envelope.closure S I X ∪ O) =
    SMTree.Envelope.closure S (RunNew.I (cut+1))
      (X ∪ O) := by
  have hSeed : X ⊆ SMTree.Envelope.closure S I X ∪ O := by
    intro x hx
    exact Or.inl ((SMTree.Envelope.subset_closure S I X) hx)
  have hSelected :=
    actual_AlgorithmRun_selected_levels_mono_of_seed_growth
      H X (SMTree.Envelope.closure S I X ∪ O)
      hSeed top RunOld RunNew (cut+1) (by omega)
  have hLevels : I ⊆ RunNew.I (cut+1) :=
    hOldHigher.trans hSelected
  exact envelope_closure_absorbs_old_closure_of_levels
    S I (RunNew.I (cut+1)) X O hLevels

/-- Concrete numerical-H+ specialization. The corrected new-root
source contains the OLD full Kpt meet/parameter closure plus ONLY
the genuinely inserted physical original Kpt nodes in W, NOT
their full prefix pools.

If I⊆RunOld.I(cut+1), literal new-run source equality is
DERIVED even though RunNew.I(cut+1) is a priori different.

Therefore the full semantic I1/I2/I3 event predicates and the
ENTIRE physical dependent old/upper L+ crossing relation are
identical between the inherited-closure presentation and its
BARE old+new original-seed presentation at the same real cut.
No no-I2 hypothesis: the relation can have true forks. -/
theorem numericH_two_runs_preCut_full_profile_absorbs_of_old_higher
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top cut : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) top)
    (hCut : cut < top)
    (hOldHigher : I ⊆ RunOld.I (cut+1)) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Zfull : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W)
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1)) (X ∪ O)
    Zfull = Zbare ∧
      (KptI1AtCut family Zfull cut ↔
        KptI1AtCut family Zbare cut) ∧
      (KptI2MeetAtCut family Zfull cut ↔
        KptI2MeetAtCut family Zbare cut) ∧
      FullPhysicalClosureCrossing family Zfull cut =
        FullPhysicalClosureCrossing family Zbare cut ∧
      (SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Zfull cut ↔
       SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Zbare cut) := by
  have hAbs :
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W) =
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (X ∪ ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) := by
    change
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (SMTree.Envelope.closure (admissibleKptSTree family) I X ∪
          ((fun w : Fin M =>
            (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) =
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (X ∪ ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W))
    exact actual_two_run_preCut_absorption_of_old_higher_levels
      (admissibleKptSTree family) (normalizedKptSMTree family)
      X ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
      I top cut RunOld RunNew hCut hOldHigher
  dsimp only
  rw [hAbs]
  exact ⟨rfl, Iff.rfl, Iff.rfl, rfl, Iff.rfl⟩

/-- A fully constructed actual CANONICAL Kpt new-root run for
one chosen cut. Choose the inherited generating levels I to be
EXACTLY the OLD run's real higher selected levels at that cut.

The physical new seed Y_cut depends on cut; no single global Y
is claimed to satisfy this formula simultaneously at all cuts.

The old-higher-retention hypothesis is automatically reflexive.
The new-run existence comes from the genuine successor-tree
canonicalAlgorithmRun, not a stipulated run witness. The result
identifies the WHOLE physical pre-cut Kpt source and all I1/I2/I3
and dependent L+ crossing data in the bare-original presentation. -/
theorem numericH_canonical_new_root_old_tail_preCut_full_profile_absorbs
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top cut : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hCut : cut < top) :
    let I : Set Nat := RunOld.I (cut+1)
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_physicalExtendedSeeds family L k M hAvoid I X W
    let RunNew : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top :=
      SMTree.Envelope.canonicalAlgorithmRun
        (normalizedKptSMTree family) Y top
    let Zfull : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1)) Y
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1)) (X ∪ O)
    Zfull = Zbare ∧
      (KptI1AtCut family Zfull cut ↔
        KptI1AtCut family Zbare cut) ∧
      (KptI2MeetAtCut family Zfull cut ↔
        KptI2MeetAtCut family Zbare cut) ∧
      FullPhysicalClosureCrossing family Zfull cut =
        FullPhysicalClosureCrossing family Zbare cut ∧
      (SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Zfull cut ↔
       SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Zbare cut) := by
  exact numericH_two_runs_preCut_full_profile_absorbs_of_old_higher
    family L k M hAvoid
    (RunOld.I (cut+1)) X W top cut RunOld
    (SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds family L k M hAvoid
        (RunOld.I (cut+1)) X W) top)
    hCut Set.Subset.rfl

/-- The genuine new-root selected-level difference has an ACTUAL
PHYSICAL witness in the BARE source generated by original old Kpt
seeds X and new physical Kpt ORIGINALS O.

If the old generating levels I occur among the old run's true
higher selected levels at cut, their preinserted old closure is
absorbed and cannot itself account for a new terminal or full
L+ crossing. All genuinely new events are witnessed in
closure_(RunNew.I(cut+1))(X∪O), not a fake seed source.

This is a necessary, NOT sufficient, event attribution; it does
not prove no new auxiliary interesting cuts or a common labelled
inverse-source orbit. -/
theorem numericH_new_selected_cut_has_bare_original_source_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (top cut : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) top)
    (hCut : cut < top)
    (hOldHigher : I ⊆ RunOld.I (cut+1))
    (hNew : cut ∈ RunNew.I cut)
    (hOld : cut ∉ RunOld.I cut) :
    let O : Set (AdmissibleKptNode family) :=
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    let Zold : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X
    let Zbare : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1)) (X ∪ O)
    (∃ z : AdmissibleKptNode family,
      z ∈ Zbare ∧ z ∉ Zold ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family Zbare cut ∧
      p ∉ FullPhysicalClosureCrossing family Zold cut) := by
  have hSeed : X ⊆ finiteNumericH_physicalExtendedSeeds
      family L k M hAvoid I X W := by
    intro z hz
    change z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X ∪
      ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
    exact Or.inl ((SMTree.Envelope.subset_closure
      (admissibleKptSTree family) I X) hz)
  have hNovel :=
    new_selected_Kpt_cut_has_new_terminal_or_full_crossing
      family X
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W)
      hSeed top cut RunOld RunNew hCut hNew hOld
  have hAbs :
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W) =
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (X ∪ ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) :=
    actual_two_run_preCut_absorption_of_old_higher_levels
      (admissibleKptSTree family) (normalizedKptSMTree family)
      X ((fun w : Fin M =>
        (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)
      I top cut RunOld RunNew hCut hOldHigher
  dsimp only at hNovel ⊢
  rw [hAbs] at hNovel
  exact hNovel

end Kk
