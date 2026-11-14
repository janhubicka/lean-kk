import Kk.ActualRunLevelProfileSync
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track E: actual Algorithm 5.4 is monotone under genuine new Kpt seeds

Unlike the conditional TWO-RUN E26 equality theorem, this result
assumes NO cross-occurrence source-profile matching at all:

  If X ⊆ Y are literal genuine Kpt seed sets and R_X, R_Y are
  ACTUAL descending AlgorithmRuns with the same top/horizon,
  then R_X.I i ⊆ R_Y.I i at EVERY stage i.

This follows from two kernel-checked generic facts:
  * the TRUE meet-and-parameter closure is monotone in both seeds
    and selected level sets;
  * the actual semantic I1/I2/I3 predicate IsInterestingAt is
    monotone in the full source closure. In the I3 case the SAME
    genuine skipping monoid map for the larger set would skip the
    smaller set, not merely a selected-front graph shadow.

No B3 converse, no E1, no bound on full closure size, and no
unproved physical new-root realization are introduced.

English-first proof and hostile checks:
  docs/track_e_monotone_seed_growth_english_audit.md
-/

namespace Kk

open SuccessorTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The ACTUAL meet-and-parameter closure increases when BOTH
its selected parameter levels and its seed nodes increase.
Nothing is restricted to selected original vertices; meets and
arbitrary dependent source parameters are included. -/
theorem envelope_closure_mono_both
    (I J : Set Nat) (X Y : Set T)
    (hIJ : I ⊆ J) (hXY : X ⊆ Y) :
    SMTree.Envelope.closure S I X ⊆
      SMTree.Envelope.closure S J Y := by
  apply SMTree.Envelope.closure_minimal
    S I X (SMTree.Envelope.closure S J Y)
  · exact hXY.trans (SMTree.Envelope.subset_closure S J Y)
  · exact SMTree.Envelope.closure_meetClosed S J Y
  · exact (SMTree.Envelope.closure_parameterClosed S J Y).mono_levels hIJ

/-- ACTUAL generic Algorithm-5.4 interestingness is monotonically
increasing with its complete physical source.

I1 and I2 retain their genuine witnesses; for I3, any ACTUAL
monoid map skipping a larger closure would also satisfy all
crossing equations of the smaller closure. No L-only B3 age-test
or fake auxiliary E is introduced. -/
theorem actual_IsInterestingAt_mono_full_source
    (H : SMTree S)
    (Z W : Set T) (hZW : Z ⊆ W) (cut : Nat)
    (hInteresting : SMTree.Envelope.IsInterestingAt H Z cut) :
    SMTree.Envelope.IsInterestingAt H W cut := by
  rcases hInteresting with hI1 | hOther
  · obtain ⟨z,hz,hlev⟩ := hI1
    exact Or.inl ⟨z,hZW hz,hlev⟩
  · rcases hOther with hI2 | hI3
    · obtain ⟨a,ha,b,hb,hComp,hMeet⟩ := hI2
      exact Or.inr (Or.inl ⟨a,hZW ha,b,hZW hb,hComp,hMeet⟩)
    · refine Or.inr (Or.inr ?_)
      rintro ⟨D,hSkip,hRespectW⟩
      apply hI3
      refine ⟨D,hSkip,?_⟩
      intro z hz hCut
      exact hRespectW (hZW hz) hCut

/-- GENUINE AlgorithmRuns on seed sets X⊆Y, over the same
(S,M)-tree and top, satisfy exact stagewise set inclusion of
selected/interesting levels. Map choices may be completely
different and no common source profile/orbit is assumed.

In particular inserting a genuinely new Kpt root can ADD but
cannot DELETE an interesting level, as long as the comparison
uses the same source-level scan horizon. -/
theorem actual_AlgorithmRun_selected_levels_mono_of_seed_growth
    (H : SMTree S)
    (X Y : Set T) (hXY : X ⊆ Y) (top : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun H X top)
    (RunY : SMTree.Envelope.AlgorithmRun H Y top) :
    ∀ i : Nat, i ≤ top → RunX.I i ⊆ RunY.I i := by
  have hDown : ∀ d : Nat, ∀ i : Nat,
      top - i = d → i ≤ top → RunX.I i ⊆ RunY.I i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdi hLe
      by_cases hTop : i = top
      · subst i
        rw [RunX.topI,RunY.topI]
      · have hLt : i < top := lt_of_le_of_ne hLe hTop
        have hNext : RunX.I (i+1) ⊆ RunY.I (i+1) :=
          ih (top-(i+1)) (by omega) (i+1) rfl (by omega)
        have hSources : SMTree.Envelope.closure S
              (RunX.I (i+1)) X ⊆
            SMTree.Envelope.closure S (RunY.I (i+1)) Y :=
          envelope_closure_mono_both
            (RunX.I (i+1)) (RunY.I (i+1)) X Y hNext hXY
        by_cases hOld :
            SMTree.Envelope.IsInterestingAt H
              (SMTree.Envelope.closure S (RunX.I (i+1)) X) i
        · have hNew :
              SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RunY.I (i+1)) Y) i :=
            actual_IsInterestingAt_mono_full_source
              H _ _ hSources i hOld
          have hOldI := (RunX.interesting_step i hLt hOld).1
          have hNewI := (RunY.interesting_step i hLt hNew).1
          rw [hOldI,hNewI]
          intro q hq
          rcases Set.mem_insert_iff.mp hq with hEq | hIn
          · exact Set.mem_insert_iff.mpr (Or.inl hEq)
          · exact Set.mem_insert_of_mem i (hNext hIn)
        · obtain ⟨_,_,_,hOldI,_⟩ :=
            RunX.noninteresting_step i hLt hOld
          have hYTail : RunY.I (i+1) ⊆ RunY.I i := by
            rcases RunY.level_step i hLt with hEq | hIns
            · rw [hEq]
            · intro q hq
              rw [hIns]
              exact Set.mem_insert_of_mem i hq
          rw [hOldI]
          exact hNext.trans hYTail
  intro i hLe
  exact hDown (top-i) i rfl hLe

/-- The final selected-level set of a genuine enlarged-seed
AlgorithmRun contains the old run's final selected-level set.
No fixed-seed hypothesis: this is new-root MONOTONICITY. -/
theorem actual_AlgorithmRun_final_levels_mono_of_seed_growth
    (H : SMTree S)
    (X Y : Set T) (hXY : X ⊆ Y) (top : Nat)
    (RunX : SMTree.Envelope.AlgorithmRun H X top)
    (RunY : SMTree.Envelope.AlgorithmRun H Y top) :
    RunX.I 0 ⊆ RunY.I 0 :=
  actual_AlgorithmRun_selected_levels_mono_of_seed_growth
    H X Y hXY top RunX RunY 0 (Nat.zero_le top)

/-- This is the LITERAL new-root-source step used by the physical
Track C construction: retain the full old meet/parameter closure
over I and ADD a set W of genuine Kpt new-root prefixes.

The former seed X embeds into the new source by the ACTUAL
least-closure inclusion. The selected-level monotonicity between
two genuine same-horizon AlgorithmRuns is then UNCONDITIONAL
on all interestingness/source-matching profiles. -/
theorem actual_Kpt_new_roots_preserve_old_interesting_levels
    {db du dd : Nat}
    (family : List (SuccessorTree.V10.NormalizedForbidden db du dd))
    (X W : Set (SuccessorTree.V10.AdmissibleKptNode family))
    (I : Set Nat) (top : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (SuccessorTree.V10.normalizedKptSMTree family) X top)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (SuccessorTree.V10.normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (SuccessorTree.V10.admissibleKptSTree family) I X ∪ W) top) :
    ∀ i : Nat, i ≤ top → RunOld.I i ⊆ RunNew.I i := by
  have hXY : X ⊆
      (SMTree.Envelope.closure
        (SuccessorTree.V10.admissibleKptSTree family) I X ∪ W) := by
    intro x hx
    exact Or.inl (SMTree.Envelope.subset_closure
      (SuccessorTree.V10.admissibleKptSTree family) I X hx)
  exact actual_AlgorithmRun_selected_levels_mono_of_seed_growth
    (SuccessorTree.V10.normalizedKptSMTree family)
    X _ hXY top RunOld RunNew

end Kk
