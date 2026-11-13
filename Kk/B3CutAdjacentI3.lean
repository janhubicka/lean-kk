import Kk.B3ClosureFibreCoherence
import Kk.B3ActualI3ExtraUpper
import Mathlib.Tactic

/-!
# Track B: any hidden genuine nonstructural I3 must omit a CUT NEIGHBOUR

English-first proof and adversarial audit:
  docs/track_b_cut_adjacent_i3_english_audit.md

Track D's no-I2 cut-visible transfer is combined with the true
closure-selected Algorithm 5.4 I3 failure theorem. If a genuine
marked closure source passes corrected B3 but the full source has
a nonstructural I3 event, a FULL-selected and FREE-CUT-ELIGIBLE
original adjacent to the cut must be unmarked.

Unlike the generic Track B extra-upper-type theorem this
witness is required to have a positive PHYSICAL ordinary-L edge
to the tested cut. We do not identify the marked selection with
the paper's proposed canonical diary.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuinely nonstructural interesting Kpt closure cut in a
finite numerical Henson model requires one *omitted cut-neighbour*
whenever an actual represented marked source passes corrected B3.

The full source is precisely the closure-selected original pool,
not every eligible original in the ambient structure.

No-I1, no-I2, a fixed original-name pool, marked source
representation and marked nonemptiness are essential hypotheses.
The conclusion is a REAL positive L edge, not a positive E bit. -/
theorem henson_represented_I3_requires_unmarked_cut_neighbour
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N) (hPositive : 0 < cut)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M,
        z ≤ (finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily ell hell) hAvoid (original v))
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ Z ∧ LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ Z ∧ ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (hInteresting : SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) Z cut)
    (Marked : Fin M → Prop)
    (hMarkedNonempty : ∃ v : Fin M, Marked v)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z cut v)
    (hMarkedB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin M,
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original Z cut v ∧
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val ∧
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true ∧
      ¬ Marked v := by
  classical
  let family := hensonForbiddenFamily ell hell
  let A := finiteNumericH (normalizedGraphModel E) k N
  let Full : Fin M → Prop :=
    closureSelectedOriginal family A hAvoid original Z cut
  have hFailure :
      ¬ (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
        family := by
    exact algorithmI3_failsCorrectedB3
      family A hAvoid original Z hPool cut hPositive
      hNoI1 hNoI2 hInteresting
  by_contra hNoWitness
  have hAllNeighboursMarked : ∀ v : Fin M, Full v →
      cut+1 ≤ A.freeLevel (original v).val →
      A.L.binary cut (original v).val (0 : Fin 1) = true →
      Marked v := by
    intro v hFull hEligible hEdge
    by_contra hNotMarked
    exact hNoWitness ⟨v,hFull,hEligible,hEdge,hNotMarked⟩
  have hPass :
      (selectedStagePoolPrescribedData A cut original Full).CorrectedB3
        family :=
    henson_fullB3_of_no_i2_marked_closure_cut_neighbours
      ell hell k hK E hLoops hSym hClique
      N cut M hCut original hAvoid Z Full Marked
      hMarkedNonempty hMarkedRepresented hNoI2
      hAllNeighboursMarked hMarkedB3
  exact hFailure hPass

/-- The same named cut-neighbour obstruction at an ACTUAL
Algorithm 5.4 selected stage: the source is exactly the run's
pre-cut closure at I(cut+1). Its interestingness follows from the
AlgorithmRun rather than being separately assumed. -/
theorem henson_algorithmRun_I3_requires_unmarked_cut_neighbour
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N cut M : Nat) (hCut : cut < N) (hPositive : 0 < cut)
    (original : Fin M → Fin N)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = top)
    (hBelow : cut < top) (hSelected : cut ∈ Run.I 0)
    (hPool : ∀ z,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X →
      ∃ v : Fin M,
        z ≤ (finiteNumericH (normalizedGraphModel E) k N).kptOriginal
          (hensonForbiddenFamily ell hell) hAvoid (original v))
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧ LevelTree.lev z = cut)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ b : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = cut)
    (Marked : Fin M → Prop)
    (hMarkedNonempty : ∃ v : Fin M, Marked v)
    (hMarkedRepresented : ∀ v : Fin M, Marked v →
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original
        (SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X) cut v)
    (hMarkedB3 :
      (selectedStagePoolPrescribedData
        (finiteNumericH (normalizedGraphModel E) k N)
        cut original Marked).CorrectedB3
          (hensonForbiddenFamily ell hell)) :
    ∃ v : Fin M,
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoid original
        (SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X) cut v ∧
      cut+1 ≤ (finiteNumericH (normalizedGraphModel E) k N).freeLevel
        (original v).val ∧
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        cut (original v).val (0 : Fin 1) = true ∧
      ¬ Marked v := by
  let family := hensonForbiddenFamily ell hell
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (Run.I (cut+1)) X
  have hInteresting : SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family) Z cut := by
    have hFinal := Run.finalLevel_interesting_of_run hTopSeed hSelected
    have hNext := Run.I_succ_eq_higher_final_of_run cut hBelow
    simpa only [Z,hNext] using hFinal
  exact henson_represented_I3_requires_unmarked_cut_neighbour
    ell hell k hK E hLoops hSym hClique
    N cut M hCut hPositive original hAvoid
    Z hPool hNoI1 hNoI2 hInteresting
    Marked hMarkedNonempty hMarkedRepresented hMarkedB3

#print axioms henson_represented_I3_requires_unmarked_cut_neighbour
#print axioms henson_algorithmRun_I3_requires_unmarked_cut_neighbour

end Kk
