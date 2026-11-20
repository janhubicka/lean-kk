import Kk.TrackDOddPlanFreeClosure
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Track D: actual cap/top Kpt seeds and free-closed Plan skip omitted odd cuts

English-first proof and sixteen hostile checks:
docs/audits/2026-11-20-track-d-top-seed-odd-plan-english.md

The seed is literally the finite numeric-H top-generation seed source,
not an arbitrarily selected front. The cap root Kpt original is a
source seed ending at the actual run height top. All its other initial
ancestors lie at even real top-generation coordinates. Hence no seed
can end at a below-top odd coordinate; the selected physical Plan
free-cut closure excludes stage-original endpoints there, and the
verified genuine odd Kpt no-I1/I2/I3 theorem gives nonselection.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- In one genuine finite Henson AlgorithmRun initialized with the
literal cap Kpt original and its chosen top-generation ancestors,
EVERY omitted odd cut below top is skipped if the proposed Plan
contains the cap's true top E-free cut, contains the actually selected
higher levels, and closes positive physical original E-free cuts.

No independent seed source, no seed-at-cut, no full I1/I2/B3 and no
equality with the final selected-level pool is assumed. -/
theorem henson_topSeeds_odd_omitted_of_closed_plan
    (ell : Nat) (hell : 2 ≤ ell)
    (k : Nat) (hK : ell ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin ell → Nat, StrictMono f ∧
      (∀ a b : Fin ell, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (root : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel root.val)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell))
      (numericHTopGenerationSeeds
        (hensonForbiddenFamily ell hell) (normalizedGraphModel E)
        k N hAvoid root blocks hWithin :
          Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel root.val))
    (a : Nat)
    (hBelow : 2*a+1 <
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel root.val)
    (hCut : 2*a+1 < N)
    (Plan : Set Nat)
    (hTopPlanned :
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel root.val
        ∈ Plan)
    (hAbove : Run.I ((2*a+1)+1) ⊆ Plan)
    (hPlanClosed : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val ∈ Plan)
    (hOmitted : 2*a+1 ∉ Plan) :
    2*a+1 ∉ Run.I 0 := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoid root blocks hWithin
  let top : Nat := A.freeLevel root.val
  let U : Finset (Fin N) := {root}
  have hX : X ⊆ ambientPrefixPool family A hAvoid
      (U : Set (Fin N)) := by
    simpa only [X, U, A, Finset.coe_singleton] using
      (numericHTopGenerationSeeds_subset_rootPool
        family K k N hAvoid root blocks hWithin)
  have hRootSeed : A.kptOriginal family hAvoid root ∈ X := by
    simp [X, numericHTopGenerationSeeds, A]
  have hTopSeed : ∃ z ∈ X, LevelTree.lev z = top := by
    refine ⟨A.kptOriginal family hAvoid root,hRootSeed,?_⟩
    rfl
  have hNoSeed : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = 2*a+1 := by
    rintro ⟨z,hz,hLev⟩
    exact (numericHTopGenerationSeeds_noOddBelowRoot
      family K k N hAvoid root blocks hWithin
      a hBelow z hz) hLev
  have hRootClosed : ∀ v : Fin N, v ∈ U →
      A.freeLevel v.val = 0 ∨ A.freeLevel v.val ∈ Plan := by
    intro v hv
    have hEq : v = root := by simpa [U] using hv
    subst v
    exact Or.inr hTopPlanned
  exact henson_actualRun_odd_omitted_of_closed_plan
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTopSeed
    a hBelow hCut
    Plan hAbove hRootClosed hPlanClosed hOmitted hNoSeed

#print axioms Kk.henson_topSeeds_odd_omitted_of_closed_plan

end Kk
