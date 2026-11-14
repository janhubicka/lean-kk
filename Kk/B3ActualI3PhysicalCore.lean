import Kk.B3ActualRunFullBadCoreIff
import SuccessorTree.V10.I3AlgorithmRunSharp
import Mathlib.Tactic

/-!
# Track D: actual nonstructural I3 forces one exactly labelled physical core

A TRUE selected (I3) level of an actual finite numerical Henson
AlgorithmRun has a failing corrected B3 test of its COMPLETE
parameter-closed pre-cut source. The existing pinned successor-tree
theorem derives this failure from actual run interestingness and
absence of both full (I1) and (I2).

The checked Track D actual full-AlgorithmRun physical-core iff
then upgrades this failure to ONE finite L-only K_ell clique core
whose ALL upper vertices have selected, eligible, physically
cut-adjacent actual originals with matching complete next-cut
ordinary L-reducts. No E is assigned to the arbitrary age witness.

English proof and hostile audit preceded the Lean declaration:
docs/audits/2026-11-14-track-d-actual-i3-physical-core-english.md

This is I3 -> physical core, not a converse, and not selected-front
relative graph-age loss or a macrodiary/source orbit theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A TRUE nonstructural I3 event in a genuine finite Henson Algorithm
5.4 run has ONE bounded forbidden K_ell ordinary-L continuation
certificate, with ALL its future vertices named by genuine eligible
physical cut-star originals of the exact COMPLETE next L type.

The complete source is the pre-cut closure Run.I(cut+1) represented
by the maintained final original pool Run.I 0; auxiliary parameters
are never replaced by selected diary active branches. -/
theorem henson_actualRun_nonstructural_I3_has_exact_physical_core
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily ell hell)
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (cut : Nat) (hPos : 0 < cut)
    (hBelow : cut < top) (hCut : cut < N)
    (hSelected : cut ∈ Run.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      LevelTree.lev z = cut)
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
      N U hAvoidA X top Run cut hCut hNoI2
    HensonPhysicalCutStarBadCore
      ell hell P.k P.N cut P.M P.E P.original P.Full := by
  classical
  intro P
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  have hCarrier : ∀ i : Nat, i ∈ K.carrier := by
    intro i
    trivial
  have hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K :=
    (hensonForbiddenFamily_avoids_iff ell hell E).2
      ⟨hLoops,hSym,hClique⟩
  have hXCanonical : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N)
      (finiteNumericH_avoids_family
        family K hCarrier k N hAvoidK) (U : Set (Fin N)) := by
    exact hX
  have hFailed :=
    numericH_algorithmRun_I3_stage_failedB3
      family K hCarrier hAvoidK k N U X hXCanonical
      top Run hTop cut hPos hBelow hCut hSelected
      hNoI1 hNoI2
  have hFullFailed :
      ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
    exact hFailed
  have hRunFull :=
    henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique N U hAvoidA
      X hX top Run cut hCut hBelow hNoI2
  exact hRunFull.2.2.mp hFullFailed

#print axioms henson_actualRun_nonstructural_I3_has_exact_physical_core

end Kk
