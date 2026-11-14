import Kk.B3ActualRunFullSourceCertification
import Kk.B3PhysicalBadCoreIff
import Mathlib.Tactic

/-!
# Track D: exact true AlgorithmRun full corrected B3 ↔ physical bad core

The previous Track D theorem applies to a Selected original-name
predicate satisfying only Selected -> genuine closure representation.
It is not automatically the ENTIRE parameter-closed closure source.

This module uses BOTH checked Track B certificates for the actual
numerical-H AlgorithmRun: exact full selected name predicate and
exhaustiveness of the actual maintained original-name pool for every
pre-cut Kpt closure node. Only after these two validations do we
identify the local no-I2 physical bad-core iff with the TRUE FULL
AlgorithmRun corrected-B3 test.

The normalized finite L-age bad core has no auxiliary E. This is
NOT the unproved selected-front graph-age loss equivalence.

English-first proof and hostile audit:
docs/audits/2026-11-14-track-d-actual-run-full-physical-core-english.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One genuine finite Henson AlgorithmRun satisfies ALL three
source-sensitive facts at its tested no-(I2) cut:

(1) FULL names are exactly the actual pre-cut closure-selected names;
(2) EVERY pre-cut closure Kpt node is represented by a maintained
    physical original from the FINAL original-name universe;
(3) failure of the resulting complete corrected-B3 age test is
    equivalent to one finite physically labelled cut-star bad core.

The first two components are essential to prevent an arbitrary
represented SUBPOOL from being misidentified as the entire full
parameter-closed AlgorithmRun source. The true pre-cut closure
uses Run.I (cut+1); only the fixed original-name carrier uses
Run.I 0. No-(I1) is not needed for this corrected-B3 equivalence. -/
theorem henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (cut : Nat) (hCut : cut < N) (hBelow : cut < top)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
    (∀ v : Fin P.M,
      P.Full v ↔ closureSelectedOriginal
        (hensonForbiddenFamily ell hell)
        P.ambient P.hAvoid P.original P.Z cut v) ∧
    (∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ P.Z →
        ∃ v : Fin P.M,
          z ≤ P.ambient.kptOriginal
            (hensonForbiddenFamily ell hell)
            P.hAvoid (P.original v)) ∧
    (¬ P.fullProfile.CorrectedB3
        (hensonForbiddenFamily ell hell) ↔
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N cut P.M P.E P.original P.Full) := by
  intro P
  have hNames :
      ∀ v : Fin P.M,
        P.Full v ↔ closureSelectedOriginal
          (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z cut v :=
    actualHensonRunCutOccurrence_fullExact
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X top Run cut hCut hNoI2
  have hPool :
      ∀ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        z ∈ P.Z →
          ∃ v : Fin P.M,
            z ≤ P.ambient.kptOriginal
              (hensonForbiddenFamily ell hell)
              P.hAvoid (P.original v) :=
    actualHensonRunCutOccurrence_poolExhaustive
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run cut hCut hBelow hNoI2
  have hCore :
      (¬ P.fullProfile.CorrectedB3
          (hensonForbiddenFamily ell hell)) ↔
        HensonPhysicalCutStarBadCore
          ell hell P.k P.N cut P.M P.E P.original P.Full :=
    henson_fullB3_failure_iff_physical_cut_star_bad_core_of_no_I2
      ell hell P.k P.hK P.E P.hLoops P.hSym P.hClique
      P.N cut P.M P.hCut P.original P.Z P.Full
      P.hAvoid P.hRepresented P.hNoI2
  exact ⟨hNames,hPool,hCore⟩

#print axioms henson_actualRun_complete_fullB3_failure_iff_physical_bad_core

end Kk
