import Kk.NumericHPrefixB3Stability
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Track E: genuine AlgorithmRun stability under physical numeric-H+ growth

This is an APPLICATION of Track C's literal prefix Kpt source coherence
to TWO actual Algorithm 5.4 runs, not just a comparison of arbitrarily
given selected-level sets. The Kpt seed set X is the SAME in both
runs, the physical base K and generation k are fixed, and N ≤ M.

The already verified generic AlgorithmRun.I_eq proves the runs have
identical selected-level sets independently of their one-level monoid
map choices. At EVERY true no-I2 pre-cut stage, the literal closure
is therefore the same set, and Track C's real finiteNumericH prefix
coherence proves FULL old/upper L+ prescribed graph and corrected-B3
stability, including all E atoms and every parameter/meet source node.

This is a physical finite prefix-extension theorem, NOT the
different-seed / same-diary common labelled orbit theorem.

English-first proof and hostile audit:
  docs/track_e_actual_run_prefix_stability_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For two real AlgorithmRuns on the SAME complete Kpt seed set X,
possibly with different one-level chosen monoid maps, finite numerical
H+ carrier growth at FIXED base K and generation k cannot change:
  (i) any selected level of either run;
  (ii) the complete old-to-next L+ prescribed source graph at any
       non-I2 actual cut, including auxiliary E, false L atoms,
       genuine meet and selected parameter records;
  (iii) the full corrected (B3) verdict at such a cut.

The next-stage source of each map is its GENUINE pre-cut run closure
and is NOT assumed equal to the other: the equality is DERIVED from
the verified AlgorithmRun recursion.

The same-seed requirement is essential. This does NOT identify
different resolved Kk diary occurrences or their labelled monoid
inverse-source orbits. -/
theorem numericH_two_actual_runs_prefix_full_source_and_B3_stable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N M : Nat) (hNM : N ≤ M)
    (hAvoidN : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidM : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidN U)
    (top : Nat)
    (R S : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    (∀ i : Nat, i ≤ top → R.I i = S.I i) ∧
      (∀ cut : Nat, cut < top →
        (¬ ∃ a : AdmissibleKptNode family,
          a ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X ∧
          ∃ b : AdmissibleKptNode family,
            b ∈ SMTree.Envelope.closure
              (admissibleKptSTree family) (R.I (cut+1)) X ∧
            SMTree.Envelope.SameComponent a b ∧
            LevelTree.lev (LevelTree.meet a b) = cut) →
        let ZR : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (cut+1)) X
        let ZS : Set (AdmissibleKptNode family) :=
          SMTree.Envelope.closure
            (admissibleKptSTree family) (S.I (cut+1)) X
        let F_N : PrescribedBoringData cut db du dd :=
          closureSelectedBoringData family
            (finiteNumericH K k N) hAvoidN
            (fun v : Fin N => v) ZR cut
        let F_M : PrescribedBoringData cut db du dd :=
          closureSelectedBoringData family
            (finiteNumericH K k M) hAvoidM
            (fun v : Fin M => v) ZS cut
        F_N.source = F_M.source ∧
          (∀ T, T ∈ F_N.source → F_N.target T = F_M.target T) ∧
          (F_N.CorrectedB3 family ↔ F_M.CorrectedB3 family)) := by
  have hLevels : ∀ i : Nat, i ≤ top → R.I i = S.I i :=
    R.I_eq S
  refine ⟨hLevels,?_⟩
  intro cut hCut hNoMeet
  have hTail : R.I (cut+1) = S.I (cut+1) :=
    hLevels (cut+1) (by omega)
  change
    (closureSelectedBoringData family
      (finiteNumericH K k N) hAvoidN
      (fun v : Fin N => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut).source =
    (closureSelectedBoringData family
      (finiteNumericH K k M) hAvoidM
      (fun v : Fin M => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (S.I (cut+1)) X) cut).source ∧
    (∀ T,
      T ∈ (closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidN
        (fun v : Fin N => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut).source →
      (closureSelectedBoringData family
        (finiteNumericH K k N) hAvoidN
        (fun v : Fin N => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut).target T =
      (closureSelectedBoringData family
        (finiteNumericH K k M) hAvoidM
        (fun v : Fin M => v)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (S.I (cut+1)) X) cut).target T) ∧
    ((closureSelectedBoringData family
      (finiteNumericH K k N) hAvoidN
      (fun v : Fin N => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut).CorrectedB3 family ↔
     (closureSelectedBoringData family
      (finiteNumericH K k M) hAvoidM
      (fun v : Fin M => v)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (S.I (cut+1)) X) cut).CorrectedB3 family)
  rw [← hTail]
  exact finiteNumericH_prefix_full_source_and_B3_stable
    family K k N M hNM hAvoidN hAvoidM U X hSeeds
    (R.I (cut+1)) cut hNoMeet

end Kk
