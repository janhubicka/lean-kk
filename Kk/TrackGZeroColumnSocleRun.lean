import Kk.TrackEZeroColumnSocleCrossing
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track G: genuine zero-column physical Kpt old-socle coverage
# constructs the entire synchronized AlgorithmRun

English proof and 15 adversarial checks committed FIRST:
docs/track_g_zero_column_socle_whole_run_english_audit_20261119.md

At every OLD-BORING cut of a true finite numerical-H+ graph
signature (db=1,du=0,dd=1), complete old Kpt ancestor coverage
of every candidate Y crossing, zero ordinary graph L column
of every eligible actual stage original, and no new terminal
imply FULL physical old/upper dependent L+/E no-novelty by
verified Track E E72. The verified G365 run transport then
CONSTRUCTS an actual target run on Y with identical selected I
and TOTAL monoid-valued F, without assuming an input Y-run.

This theorem does NOT construct those geometric hypotheses
for the proposed unbounded resolved diary, a common labelled
inverse-source orbit, or a sharp big Ramsey degree theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- The complete Kpt source old-socle matching problem on ZERO
ordinary-L columns suffices for actual whole-run transport.
The source-matching hypothesis is at the complete *old Kpt ancestor*,
not the ordinary graph reduct, and is required only at cuts that
are genuinely boring in the old full-closure AlgorithmRun. -/
theorem finiteNumericH_graph_zero_columns_old_socle_transport_whole_run
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hSym : ∀ i j : Nat,
      (finiteNumericH K k N).L.binary i j (0 : Fin 1) =
        (finiteNumericH K k N).L.binary j i (0 : Fin 1))
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hZeroStage : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      ∀ v : Fin N,
        v ∈ hStageOriginals K k N U (R.I (cut+1)) →
        cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
        (finiteNumericH K k N).L.binary
          cut v.val (0 : Fin 1) = false)
    (hOldSocle : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y →
        ∀ (hZCross : cut < LevelTree.lev z),
          ∃ w : AdmissibleKptNode family,
            w ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            ∃ (hWCross : cut < LevelTree.lev w),
              LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
                LevelTree.ancestor w cut (Nat.le_of_lt hWCross))
    (hNoNewTerminal : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      ¬ KptI1AtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y) cut) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F := by
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY top R
  intro cut hCut hOldBoring
  exact finiteNumericH_candidate_zero_stage_noNovelty_of_socle_and_noI1
    family K k N hAvoid hSym U X Y hXY hY
    top R cut
    (hZeroStage cut hCut hOldBoring)
    (hOldSocle cut hCut hOldBoring)
    (hNoNewTerminal cut hCut hOldBoring)

end Kk
