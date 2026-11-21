import Kk.TrackGZeroColumnFactorMismatchSocle
import Kk.TrackGExactFactorBadWitness
import Mathlib.Tactic

/-!
# Track G: geometric trichotomy of exact old-factor Bad cuts
# at genuine zero ordinary-L finite numerical-H+ graph stages.

English proof and 15 hostile checks FIRST:
docs/track_g_zero_stage_exact_factor_bad_trichotomy_english_audit_20261121.md

The verified G432 exact Bad witness decomposition has three
branches: actual terminal I1, actual same-component meet I2,
or one Kpt crossing violating the UNIQUE old total factor.
At true zero ordinary graph-L stages, verified G445 turns
the third branch into a physical MISSING OLD COMPLETE Kpt
lower-ancestor SOCLE witness, without any target run.

The theorem is conditional on actual zero-stage geometry and
exact full candidate source indexing at the cut. It does NOT
bound exceptional cut number, construct a labelled inverse
source, or prove a sharp Kk-free big Ramsey degree.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- At a genuine full ZERO ordinary graph-L stage, every
EXACT factor-Bad cut has one of three REAL physical obstructions:
a complete candidate Kpt terminal at cut, a genuine I2
same-component meet at cut, or one crossing candidate Kpt
node having NO old LIVE source node with the same COMPLETE
OLD Kpt ancestor at cut.

All auxiliary dependent E and negative L data are retained.
Target enumeration need only be exact, not injective.
No target AlgorithmRun is assumed. -/
theorem finiteNumericH_zero_stage_exact_factor_bad_has_three_physical_witnesses
    (family : List (NormalizedForbidden 1 0 1))
    (K : AgeTestModel 1 0 1) (k N Q : Nat)
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
    (node : Fin Q → AdmissibleKptNode family)
    (live : Nat → Fin Q → Bool)
    (cut : Nat)
    (hExactY : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ↔
      ∃ j : Fin Q, node j = z ∧ live cut j = true)
    (hZeroStage : ∀ v : Fin N,
      v ∈ hStageOriginals K k N U (R.I (cut+1)) →
      cut+1 ≤ (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).L.binary
        cut v.val (0 : Fin 1) = false)
    (hBad : cut ∈ kptExactOldFactorBadCuts
      family X top R node live) :
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      LevelTree.lev z = cut) ∨
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      ∃ w : AdmissibleKptNode family,
        w ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ∧
        SMTree.Envelope.SameComponent z w ∧
        LevelTree.lev (LevelTree.meet z w) = cut) ∨
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      ∃ (hZCross : cut < LevelTree.lev z),
        ¬ ∃ w : AdmissibleKptNode family,
          w ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ (hWCross : cut < LevelTree.lev w),
            LevelTree.ancestor z cut (Nat.le_of_lt hZCross) =
              LevelTree.ancestor w cut (Nat.le_of_lt hWCross)) := by
  obtain ⟨hCut,hOldBoring,_hNotCompat⟩ :=
    (mem_kptExactOldFactorBadCuts
      family X top R node live cut).mp hBad
  obtain ⟨D,_hSkip,hFactor,hCases⟩ :=
    kpt_exact_factor_bad_has_terminal_meet_or_mismatch
      family X top R node live cut hBad
  rcases hCases with hTerminal | hMeet | hMismatch
  · obtain ⟨j,hLive,hLevel⟩ := hTerminal
    have hz : node j ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (hExactY (node j)).mpr ⟨j,rfl,hLive⟩
    exact Or.inl ⟨node j,hz,hLevel⟩
  · obtain ⟨j,l,hLiveJ,hLiveL,hSame,hMeetLev⟩ := hMeet
    have hj : node j ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (hExactY (node j)).mpr ⟨j,rfl,hLiveJ⟩
    have hl : node l ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (hExactY (node l)).mpr ⟨l,rfl,hLiveL⟩
    exact Or.inr (Or.inl
      ⟨node j,hj,node l,hl,hSame,hMeetLev⟩)
  · obtain ⟨j,hLive,hCross,hDiff⟩ := hMismatch
    have hz : node j ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y :=
      (hExactY (node j)).mpr ⟨j,rfl,hLive⟩
    have hMissing :=
      finiteNumericH_zero_stage_old_factor_mismatch_has_no_old_socle
        family K k N hAvoid hSym U X Y hXY hY
        top cut R hCut hOldBoring hZeroStage
        D hFactor (node j) hz hCross hDiff
    exact Or.inr (Or.inr
      ⟨node j,hz,hCross,hMissing⟩)

end Kk
