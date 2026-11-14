import Kk.PhysicalI3CrossingInvariance
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track E: synchronize the actual selected-level sets of two Kpt runs

This uses the ACTUAL AlgorithmRun interesting/noninteresting recursion,
not an abstract assumed diary state transition.

The two seed sets and all chosen one-level Kpt monoid maps may differ.
Conditional equality of the genuine terminal-node flag and the entire
physical old/upper L+ crossing relation at each stage where the
already-selected higher levels agree makes their actual IsInterestingAt
decisions agree, by the preceding monoid-level I3 transfer.

Backward induction yields exact equality of every selected-level set,
without an E1 or same-seeds hypothesis. This is the level-only diary
skeleton, not a fully labelled inverse source or common monoid orbit.

English-first proof and hostile audit:
  docs/track_e_priority_cut_comparison_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- Two genuine Algorithm 5.4 Kpt runs with DIFFERENT seed sets
have exactly the SAME selected-level sets if their complete local
physical source profiles agree whenever the next/higher selected
level sets have already been matched.

The compared local profile consists of:
  (1) the actual full-closure terminal I1 node-existence flag; and
  (2) the complete old/upper L+ crossing relation of the actual
      meet-and-parameter-closed pre-cut sources, including auxiliary E.

There is NO assumption of no I2, no B3, no (E1), no chosen shape
map equality, and no common labelled Kpt source orbit.
The monoid I3 decision is derived by PhysicalI3CrossingInvariance;
the descending recursion is the genuine AlgorithmRun interface. -/
theorem two_actual_Kpt_runs_level_sets_eq_of_stagewise_full_profiles
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (S : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hStage : ∀ cut : Nat, cut < top →
      R.I (cut+1) = S.I (cut+1) →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (S.I (cut+1)) Y) cut) ∧
      (FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X) cut =
       FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (S.I (cut+1)) Y) cut)) :
    ∀ i : Nat, i ≤ top → R.I i = S.I i := by
  have hInduct : ∀ d : Nat, ∀ i : Nat,
      top-i = d → i ≤ top → R.I i = S.I i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdi hLe
      by_cases hTop : i = top
      · subst i
        rw [R.topI, S.topI]
      · have hLt : i < top := lt_of_le_of_ne hLe hTop
        have hNext : R.I (i+1) = S.I (i+1) := by
          exact ih (top-(i+1)) (by omega) (i+1) rfl (by omega)
        obtain ⟨hTerminal,hCross⟩ := hStage i hLt hNext
        let ZR : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (i+1)) X
        let ZS : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure (admissibleKptSTree family)
            (S.I (i+1)) Y
        have hInteresting :
            SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family) ZR i ↔
            SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family) ZS i :=
          kpt_actual_interesting_iff_of_terminal_and_crossing_eq
            family ZR ZS i hTerminal hCross
        by_cases hR : SMTree.Envelope.IsInterestingAt
            (normalizedKptSMTree family) ZR i
        · have hS : SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family) ZS i :=
            hInteresting.mp hR
          have hRI := (R.interesting_step i hLt hR).1
          have hSI := (S.interesting_step i hLt hS).1
          rw [hRI, hSI, hNext]
        · have hS : ¬ SMTree.Envelope.IsInterestingAt
              (normalizedKptSMTree family) ZS i :=
            fun h => hR (hInteresting.mpr h)
          obtain ⟨_,_,_,hRI,_⟩ := R.noninteresting_step i hLt hR
          obtain ⟨_,_,_,hSI,_⟩ := S.noninteresting_step i hLt hS
          rw [hRI, hSI, hNext]
  intro i hLe
  exact hInduct (top-i) i rfl hLe

/-- A one-line checkpoint at the FINAL level set: the actual
selected-level diary skeleton is independent of both the initial
seed-set choice and the selected one-level monoid maps whenever
the stagewise FULL Kpt source-profile matching premise holds.

This is a consequence of the preceding theorem, not a new
unconditional diary-equivalence assertion. -/
theorem two_actual_Kpt_runs_final_level_sets_eq_of_stagewise_profiles
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (S : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (hStage : ∀ cut : Nat, cut < top →
      R.I (cut+1) = S.I (cut+1) →
      (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X) cut ↔
       KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (S.I (cut+1)) Y) cut) ∧
      (FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (cut+1)) X) cut =
       FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (S.I (cut+1)) Y) cut)) :
    R.I 0 = S.I 0 := by
  exact two_actual_Kpt_runs_level_sets_eq_of_stagewise_full_profiles
    family X Y top R S hStage 0 (Nat.zero_le top)

end Kk
