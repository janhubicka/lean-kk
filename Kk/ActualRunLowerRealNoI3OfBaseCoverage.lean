import Kk.B3LowerRealBaseCoverage
import Kk.B3ActualI3PhysicalCore
import Kk.B3ActualRunFullBadCoreIff
import Mathlib.Tactic

/-!
# Track D: no genuine nonstructural I3 at a physically covered lower-real cut

English-first proof and hostile audit committed BEFORE Lean:
docs/audits/2026-11-16-track-d-actual-run-no-i3-base-cover-english.md

This is the local no-I3 criterion for ONE real numerical Henson AlgorithmRun
cut c=hPosition k idx g with g<k, at the TRUE complete pre-cut Kpt closure
Z=closure(Run.I(c+1),X), not a selected diary active shadow.

If full structural I1 and I2 are absent, and a genuinely represented
marked source covers all FULL positive higher-generation base-neighbours
and passes corrected B3 on its actually CHOSEN upper L types, then the
full source passes B3 (verified physical-base transfer). Selection of c
would force true I3 and hence a full physical forbidden clique core,
contradicting that full corrected B3. Thus c is not selected.

NO claim that arbitrary small-independent records satisfy the
base-coverage, marked B3 or structural exclusion hypotheses.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A real lower-generation physical cut cannot be selected by one
true finite Henson numerical-H AlgorithmRun once ALL THREE actual
application gates hold at that SAME full source:
(1) no full I1/I2; (2) every full higher-generation physical
positive base neighbour is in a represented Marked source; and
(3) the actual CHOSEN Marked corrected B3 test passes.

The source uses Run.I (cut+1); only its fixed actual finite
name carrier uses Run.I 0. The marked pool need not be nonempty.

This is a conditional single-cut I3 elimination theorem,
not the small-independent all-cut source orbit or BRD bound. -/
theorem henson_actualRun_lower_real_unselected_of_base_covered_marked_B3
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
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      LevelTree.lev z = hPosition k idx g)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (hPosition k idx g+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (hPosition k idx g+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = hPosition k idx g) :
    let P := actualHensonRunCutOccurrence
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X top Run (hPosition k idx g) hCut hNoI2
    ∀ (Marked : Fin P.M → Prop),
      (∀ v : Fin P.M, Marked v →
        closureSelectedOriginal (hensonForbiddenFamily ell hell)
          P.ambient P.hAvoid P.original P.Z (hPosition k idx g) v) →
      (∀ v : Fin P.M, P.Full v →
        ∀ j m : Nat, idx < j → g < m → m ≤ k →
          (P.original v).val = hPosition k j m →
          E idx j = true → Marked v) →
      (selectedStagePoolPrescribedData P.ambient (hPosition k idx g)
        P.original Marked).CorrectedB3 (hensonForbiddenFamily ell hell) →
      hPosition k idx g ∉ Run.I 0 := by
  classical
  intro P Marked hMarkedRepresented hBaseCovered hMarkedB3
  have hFullB3 :
      P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) := by
    exact henson_fullB3_of_lower_real_base_covered_marked_source
      ell hell k hK E hLoops hSym hClique
      N idx g P.M hg hCut P.original P.hAvoid P.Z P.Full Marked
      hMarkedRepresented P.hNoI2 hBaseCovered hMarkedB3
  intro hSelected
  have hPhysical :
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N (hPosition k idx g)
        P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run hTop
      (hPosition k idx g) hPos hBelow hCut hSelected hNoI1 hNoI2
  have hFullFailure :
      ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
    (henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoidA X hX top Run (hPosition k idx g)
      hCut hBelow hNoI2).2.2.mpr hPhysical
  exact hFullFailure hFullB3

#print axioms henson_actualRun_lower_real_unselected_of_base_covered_marked_B3

end Kk
