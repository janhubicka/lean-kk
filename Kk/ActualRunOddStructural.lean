import Kk.B3ActualI3PhysicalCore
import Kk.NumericHStructuralCutClassifier
import Kk.B3CutStarNormalForm
import Mathlib.Tactic

/-!
# Track D: selected genuine ODD numerical-H cut forces structural I1 or I2

English proof and 16 hostile source/quantifier checks committed first:
docs/audits/2026-11-15-track-d-actual-run-odd-structural-english.md

The checked true-run nonstructural I3 theorem gives a FULL physical
forbidden clique core when a positive cut is selected and complete
I1 and I2 are absent. Checked full-source finite B3 equivalence turns
it into a failed complete selected-stage B3. This yields an ACTUAL
eligible positive ordinary-L cut neighbour, impossible at any odd
numerical-H coordinate because hNumericBinary_odd_left_false.

The result is about the COMPLETE parameter-closed pre-cut Kpt source:
odd-cut selection -> genuine structural I1 or I2. It is NOT an
assertion that all odd cuts may be skipped, nor a macrodiary BRD result.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At an actual Henson numerical-H AlgorithmRun, an ODD physical
cut is NOT selected if the FULL pre-cut Kpt meet-and-parameter
closure has neither an I1 endpoint nor an I2 competing meet.

No claim about selected diary-shadow types or full source orbits.
-/
theorem henson_numericH_odd_cut_unselected_of_no_I1_I2
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat) (U : Finset (Fin N))
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
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (hNoI1 : ¬ KptI1AtCut (hensonForbiddenFamily ell hell)
      (SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I ((2*a+1)+1)) X) (2*a+1))
    (hNoI2 : ¬ KptI2MeetAtCut (hensonForbiddenFamily ell hell)
      (SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I ((2*a+1)+1)) X) (2*a+1)) :
    2*a+1 ∉ Run.I 0 := by
  classical
  intro hSelected
  let cut : Nat := 2*a+1
  have hPos : 0 < cut := by
    dsimp [cut]
    omega
  have hBelow' : cut < top := hBelow
  have hCut' : cut < N := hCut
  have hNoI1' : ¬ ∃ z : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      LevelTree.lev z = cut := hNoI1
  have hNoI2' : ¬ ∃ u : AdmissibleKptNode (hensonForbiddenFamily ell hell),
      u ∈ SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X ∧
      ∃ v : AdmissibleKptNode (hensonForbiddenFamily ell hell),
        v ∈ SMTree.Envelope.closure
          (admissibleKptSTree (hensonForbiddenFamily ell hell))
          (Run.I (cut+1)) X ∧
        SMTree.Envelope.SameComponent u v ∧
        LevelTree.lev (LevelTree.meet u v) = cut := hNoI2
  let P := actualHensonRunCutOccurrence
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X top Run cut hCut' hNoI2'
  have hPhysical :
      HensonPhysicalCutStarBadCore
        ell hell P.k P.N cut P.M P.E P.original P.Full :=
    henson_actualRun_nonstructural_I3_has_exact_physical_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      cut hPos hBelow' hCut' hSelected hNoI1' hNoI2'
  have hIff :=
    henson_actualRun_complete_fullB3_failure_iff_physical_bad_core
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run cut hCut' hBelow' hNoI2'
  have hFailure :
      ¬ P.fullProfile.CorrectedB3 (hensonForbiddenFamily ell hell) :=
    hIff.2.2.mpr hPhysical
  obtain ⟨v,_hFull,_hFree,hPositive⟩ :=
    henson_failedSelectedB3_has_eligible_cut_neighbour
      ell hell k hK E hLoops hSym hClique
      N cut P.M hCut' P.original P.Full hFailure
  have hZero :
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (2*a+1) (P.original v).val (0 : Fin 1) = false := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (2*a+1) (P.original v).val (0 : Fin 1) = false
    exact hNumericBinary_odd_left_false
      (normalizedGraphModel E).binary k a (P.original v).val (0 : Fin 1)
  have hPositive' :
      (finiteNumericHL (normalizedGraphModel E) k N).binary
        (2*a+1) (P.original v).val (0 : Fin 1) = true := hPositive
  rw [hZero] at hPositive'
  cases hPositive'

/-- In the TRUE full-closure Henson AlgorithmRun, every selected
physical ODD cut below top is explained by at least one of the
two structural events I1 (node endpoint at the cut) or I2
(competing meet at that cut). This is an inclusive disjunction.

The odd numerical H ordinary L zero does NOT eliminate auxiliary
E-parameters: they are precisely why odd structural cuts may occur. -/
theorem henson_numericH_odd_selected_requires_structural_I1_or_I2
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat) (U : Finset (Fin N))
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
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (hSelected : 2*a+1 ∈ Run.I 0) :
    let Z := SMTree.Envelope.closure
      (admissibleKptSTree (hensonForbiddenFamily ell hell))
      (Run.I ((2*a+1)+1)) X
    KptI1AtCut (hensonForbiddenFamily ell hell) Z (2*a+1) ∨
      KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z (2*a+1) := by
  classical
  intro Z
  by_contra hNot
  have hNoI1 :
      ¬ KptI1AtCut (hensonForbiddenFamily ell hell) Z (2*a+1) := by
    intro hI1
    exact hNot (Or.inl hI1)
  have hNoI2 :
      ¬ KptI2MeetAtCut (hensonForbiddenFamily ell hell) Z (2*a+1) := by
    intro hI2
    exact hNot (Or.inr hI2)
  have hNotSelected :=
    henson_numericH_odd_cut_unselected_of_no_I1_I2
      ell hell k hK E hLoops hSym hClique
      N U hAvoid X hX top Run hTop
      a hBelow hCut hNoI1 hNoI2
  exact hNotSelected hSelected

#print axioms henson_numericH_odd_cut_unselected_of_no_I1_I2
#print axioms henson_numericH_odd_selected_requires_structural_I1_or_I2

end Kk
