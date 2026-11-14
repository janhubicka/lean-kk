import Kk.NewRootMonotoneAbsorptionBridge
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track E: no spurious LOWER actual AlgorithmRun levels from old closure seeds

Let Ybare = X∪O and Yfull = closure_I X ∪ O be two genuinely
different Kpt/STree seed presentations, and let two REAL same-top
AlgorithmRuns be given on these seed sets.

Assume all inherited old parameter levels I were already selected
by the BARE run, and all lie above boundary c. If the two runs
already agree at the chosen HIGHER boundary c+1, a descending
induction proves they agree at EVERY subsequent LOWER level.

At each cut i≤c, the matched higher selected sets J contain
the inherited generating set I by the real run-tail identity.
Least full meet/parameter closure absorption then gives LITERAL
equality of genuine pre-cut sources and hence the entire semantic
I1/I2/I3 decisions. The true AlgorithmRun fields propagate the
selected-level equality.

A three-run corollary DISCHARGES the Bare-run retention assumption
from a real old run on X via verified seed-growth monotonicity.

No selected-shadow graph-age surrogate, no no-I2/B3 assumption,
no equality of monoid maps and no common labelled inverse-source
orbit are claimed.

English proof and hostile cases committed before Lean:
  docs/track_e_new_root_monotone_absorption_english_audit.md
-/

namespace Kk

open SuccessorTree

universe u v

/-- In the ACTUAL descending algorithm, two alternative initial
seed presentations X∪O and closure_I X∪O cannot choose different
lower interesting levels IF they agree at the higher boundary
c+1, the bare run selected I, and I lies STRICTLY above c.

The proof compares REAL full meet/parameter Kpt sources at each
step and derives the IsInterestingAt equivalence, including
monoid non-skippable I3, from literal equality of those sources.

This is a tail-level stability theorem, not a globally valid
claim that preinserting arbitrary closure is harmless at all
cut levels. -/
theorem actual_two_runs_lower_levels_eq_after_old_closure_absorption
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label) (H : SMTree S)
    (X O : Set T) (I : Set Nat)
    (top boundary : Nat)
    (RunBare : SMTree.Envelope.AlgorithmRun H (X ∪ O) top)
    (RunFull : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S I X ∪ O) top)
    (hBoundary : boundary < top)
    (hHigherEq : RunBare.I (boundary+1) =
      RunFull.I (boundary+1))
    (hISelected : I ⊆ RunBare.I 0)
    (hAbove : ∀ q : Nat, q ∈ I → boundary < q) :
    ∀ i : Nat, i ≤ boundary → RunBare.I i = RunFull.I i := by
  have hDown : ∀ d : Nat, ∀ i : Nat,
      boundary+1-i = d → i ≤ boundary+1 →
      RunBare.I i = RunFull.I i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdist hLe
      by_cases hBoundaryStage : i = boundary+1
      · subst i
        exact hHigherEq
      · have hTested : i ≤ boundary := by omega
        have hCutTop : i < top := by omega
        have hNext : RunBare.I (i+1) = RunFull.I (i+1) :=
          ih (boundary+1-(i+1)) (by omega) (i+1) rfl (by omega)
        have hIJ : I ⊆ RunBare.I (i+1) := by
          intro q hq
          rw [RunBare.I_eq_final_tail_of_run (i+1) (by omega)]
          refine ⟨hISelected hq,?_⟩
          have hqAbove := hAbove q hq
          omega
        have hAbs :
            SMTree.Envelope.closure S (RunBare.I (i+1))
              (SMTree.Envelope.closure S I X ∪ O) =
            SMTree.Envelope.closure S (RunBare.I (i+1))
              (X ∪ O) :=
          envelope_closure_absorbs_old_closure_of_levels
            S I (RunBare.I (i+1)) X O hIJ
        have hSourceEq :
            SMTree.Envelope.closure S (RunBare.I (i+1))
              (X ∪ O) =
            SMTree.Envelope.closure S (RunFull.I (i+1))
              (SMTree.Envelope.closure S I X ∪ O) := by
          calc
            SMTree.Envelope.closure S (RunBare.I (i+1)) (X ∪ O) =
                SMTree.Envelope.closure S (RunBare.I (i+1))
                  (SMTree.Envelope.closure S I X ∪ O) := hAbs.symm
            _ = SMTree.Envelope.closure S (RunFull.I (i+1))
                  (SMTree.Envelope.closure S I X ∪ O) := by rw [hNext]
        by_cases hBare :
            SMTree.Envelope.IsInterestingAt H
              (SMTree.Envelope.closure S (RunBare.I (i+1))
                (X ∪ O)) i
        · have hFull :
              SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RunFull.I (i+1))
                  (SMTree.Envelope.closure S I X ∪ O)) i := by
            rw [← hSourceEq]
            exact hBare
          have hStepBare := (RunBare.interesting_step i hCutTop hBare).1
          have hStepFull := (RunFull.interesting_step i hCutTop hFull).1
          rw [hStepBare,hStepFull,hNext]
        · have hFull :
              ¬ SMTree.Envelope.IsInterestingAt H
                (SMTree.Envelope.closure S (RunFull.I (i+1))
                  (SMTree.Envelope.closure S I X ∪ O)) i := by
            intro h
            exact hBare (by rw [hSourceEq]; exact h)
          obtain ⟨_,_,_,hStepBare,_⟩ :=
            RunBare.noninteresting_step i hCutTop hBare
          obtain ⟨_,_,_,hStepFull,_⟩ :=
            RunFull.noninteresting_step i hCutTop hFull
          rw [hStepBare,hStepFull,hNext]
  intro i hLe
  exact hDown (boundary+1-i) i rfl (by omega)

/-- The bare-run inherited-level selection hypothesis of the
preceding theorem need NOT be independently postulated if there
is a TRUE OLD AlgorithmRun on X that already selected I.

Since X⊆X∪O, the verified real run seed-monotonicity proves
I⊆RunOld.I0⊆RunBare.I0, irrespective of the two runs'
monoid-map choices. Thus only the higher-boundary agreement
and the actual old generating levels above the boundary need
to be checked.

All THREE actual runs use the same Kpt source-level top.
The result concerns selected-level equality BELOW boundary,
not equality of complete labelled envelopes or their maps. -/
theorem actual_three_runs_lower_levels_eq_of_old_selected_generators
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label) (H : SMTree S)
    (X O : Set T) (I : Set Nat)
    (top boundary : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun H X top)
    (RunBare : SMTree.Envelope.AlgorithmRun H (X ∪ O) top)
    (RunFull : SMTree.Envelope.AlgorithmRun H
      (SMTree.Envelope.closure S I X ∪ O) top)
    (hBoundary : boundary < top)
    (hHigherEq : RunBare.I (boundary+1) =
      RunFull.I (boundary+1))
    (hOldSelected : I ⊆ RunOld.I 0)
    (hAbove : ∀ q : Nat, q ∈ I → boundary < q) :
    ∀ i : Nat, i ≤ boundary → RunBare.I i = RunFull.I i := by
  have hSeed : X ⊆ X ∪ O := by
    intro x hx
    exact Or.inl hx
  have hOldToBare :=
    actual_AlgorithmRun_final_levels_mono_of_seed_growth
      H X (X ∪ O) hSeed top RunOld RunBare
  have hISelected : I ⊆ RunBare.I 0 :=
    hOldSelected.trans hOldToBare
  exact actual_two_runs_lower_levels_eq_after_old_closure_absorption
    S H X O I top boundary RunBare RunFull
    hBoundary hHigherEq hISelected hAbove

end Kk
