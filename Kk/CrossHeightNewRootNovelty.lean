import Kk.AlgorithmRunCrossHeightMonotonicity
import Kk.NewSourceEventWitness
import Mathlib.Tactic

/-!
# Track E: new dependent L+ source witnesses for true growing-height runs

Cross-height selected-level monotonicity has a REAL old-top seed guard.
At a cut STRICTLY BELOW oldTop, if the taller actual new-root run
selects the cut but the old run does not, the genuine full Kpt
new-root source adds a terminal I1 node or a full old/upper L+
physical crossing pair, including E and negative atoms.

English-first proof and hostile audit:
  docs/track_e_crossheight_new_root_novelty_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The exact two-way NEW-CUT WITNESS theorem in two actual finite
or infinite Kpt AlgorithmRuns. No chosen mono-map equality, no
relative graph age and no extra B3 profile matching is assumed.

At any cut selected by the larger run but NOT by the smaller
run (at its actual AlgorithmRun step), at least ONE new physical
source event is forced:
  * terminal I1 at a genuinely newly added closure node, OR
  * an old/upper COMPLETE dependent L+ crossing pair not present
    in the smaller pre-cut closure.

The two pre-cut closure sources come from their ACTUAL different
selected-level sets, not from an artificially fixed I.
All shape maps in the I3 proof belong to the genuine Kpt monoid. -/
theorem crossheight_new_selected_Kpt_cut_has_new_terminal_or_full_crossing
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
    (hSelectedNew : cut ∈ RunY.I cut)
    (hNotSelectedOld : cut ∉ RunX.I cut) :
    let ZX : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunX.I (cut+1)) X
    let ZY : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunY.I (cut+1)) Y
    (∃ z : AdmissibleKptNode family,
      z ∈ ZY ∧ z ∉ ZX ∧ LevelTree.lev z = cut) ∨
    (∃ p : PartialTypeWithE cut db du dd ×
        PartialTypeWithE (cut+1) db du dd,
      p ∈ FullPhysicalClosureCrossing family ZY cut ∧
      p ∉ FullPhysicalClosureCrossing family ZX cut) := by
  classical
  let H := normalizedKptSMTree family
  let ZX : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunX.I (cut+1)) X
  let ZY : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunY.I (cut+1)) Y
  have hLevels := envelope_algorithmRun_selected_levels_mono_seed_height
    H X Y hXY oldTop newTop hTopLe hTopSeed RunX RunY
  have hNext : RunX.I (cut+1) ⊆ RunY.I (cut+1) :=
    hLevels (cut+1) (by omega)
  have hSource : ZX ⊆ ZY :=
    envelope_closure_mono_both
      (RunX.I (cut+1)) (RunY.I (cut+1)) X Y hNext hXY
  have hFullSub :
      FullPhysicalClosureCrossing family ZX cut ⊆
      FullPhysicalClosureCrossing family ZY cut :=
    full_physical_crossing_mono_of_source_subset
      family ZX ZY hSource cut
  have hOldBoring : ¬ SMTree.Envelope.IsInterestingAt H ZX cut := by
    intro hOldInteresting
    have hStep := (RunX.interesting_step cut hCut hOldInteresting).1
    have hSelected : cut ∈ RunX.I cut := by
      rw [hStep]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hNotSelectedOld hSelected
  have hNewInteresting : SMTree.Envelope.IsInterestingAt H ZY cut := by
    by_contra hBoring
    obtain ⟨D,hSkip,hCross,hNoInsert,hMap⟩ :=
      RunY.noninteresting_step cut (by omega) hBoring
    have hAtNext : cut ∈ RunY.I (cut+1) := by
      rw [←hNoInsert]
      exact hSelectedNew
    have hBounds := RunY.I_mem_bounds
      (cut+1) (by omega) cut hAtNext
    omega
  have hNoI1Old : ¬ KptI1AtCut family ZX cut := by
    intro hNode
    exact hOldBoring (Or.inl hNode)
  by_cases hNewI1 : KptI1AtCut family ZY cut
  · obtain ⟨z,hZ,hLevel⟩ := hNewI1
    left
    refine ⟨z,hZ,?_,hLevel⟩
    intro hOldZ
    exact hNoI1Old ⟨z,hOldZ,hLevel⟩
  · right
    by_contra hNoNewPair
    have hReverse :
        FullPhysicalClosureCrossing family ZY cut ⊆
        FullPhysicalClosureCrossing family ZX cut := by
      intro p hp
      by_contra hNotOld
      exact hNoNewPair ⟨p,hp,hNotOld⟩
    have hFullEq :
        FullPhysicalClosureCrossing family ZX cut =
        FullPhysicalClosureCrossing family ZY cut :=
      Set.Subset.antisymm hFullSub hReverse
    have hTerminalEq : KptI1AtCut family ZX cut ↔
        KptI1AtCut family ZY cut := by
      constructor
      · intro h
        exact False.elim (hNoI1Old h)
      · intro h
        exact False.elim (hNewI1 h)
    have hInterestingEq :=
      kpt_actual_interesting_iff_of_terminal_and_crossing_eq
        family ZX ZY cut hTerminalEq hFullEq
    exact hOldBoring (hInterestingEq.mpr hNewInteresting)



/-- At a genuine growing-top physical numerical-H+ new-root stage,
all NEW interesting-cut physical witnesses below the old top
can be found already in the closure of the BARE old original
seeds and inserted genuinely NEW Kpt originals, not in the
bookkeeping pre-insertion of old meet/parameter closure.

Unlike the older theorem requiring cut below EVERY level of
RunOld.I 0, this uses only the actual OLD HIGHER selected levels
I ⊆ RunOld.I(cut+1). This works even with an I2 crossing fork
and without a corrected B3 assumption.

The actual new-root seeds are ORIGINAL-only, not the (false)
entire-prefix source that would force all lower I1 cuts. -/
theorem numericH_crossheight_extra_cut_has_bare_original_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd)
    (k M : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (W : Set (Fin M))
    (oldTop newTop cut : Nat)
    (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W) newTop)
    (hCut : cut < oldTop)
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
    exact Or.inl ((SMTree.Envelope.subset_closure
      (admissibleKptSTree family) I X) hz)
  have hNovel :=
    crossheight_new_selected_Kpt_cut_has_new_terminal_or_full_crossing
      family X
      (finiteNumericH_physicalExtendedSeeds
        family L k M hAvoid I X W)
      hSeed oldTop newTop cut
      hTopLe hTopSeed RunOld RunNew hCut hNew hOld
  have hAboveNew : I ⊆ RunNew.I (cut+1) := by
    have hLevels :=
      envelope_algorithmRun_selected_levels_mono_seed_height
        (normalizedKptSMTree family)
        X (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W)
        hSeed oldTop newTop hTopLe hTopSeed RunOld RunNew
        (cut+1) (by omega)
    exact hOldHigher.trans hLevels
  have hAbs :
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (finiteNumericH_physicalExtendedSeeds
          family L k M hAvoid I X W) =
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1))
        (X ∪ ((fun w : Fin M =>
          (finiteNumericH L k M).kptOriginal family hAvoid w) '' W)) :=
    finiteNumericH_newRoot_closure_absorption
      family L k M hAvoid I (RunNew.I (cut+1)) X W hAboveNew
  dsimp only at hNovel ⊢
  rw [hAbs] at hNovel
  exact hNovel

end Kk
