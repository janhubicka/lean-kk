import Kk.TrackDOddStageNoFreeEnd
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Track D: descending Plan free-cut closure makes omitted ODD cuts boring

English-first mathematical proof and seventeen hostile checks:
docs/audits/2026-11-20-track-d-odd-plan-closure-english.md

At a true pre-cut stage I=Run.I(c+1), a physically represented original
is either a root name U or a selected positive-free-level original.
If all root free cuts are retained and the proposed Plan retains each
positive selected original's actual free E cut, I subset Plan implies
that NO actual stage original ends at an omitted cut c. Nothing about
Run.I(0), selected diary ages or full original pool equality is assumed.

The exact genuine top-generation source also has no ODD seed below its
root level, independent of whether any intermediate real generation
is retained.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For ANY finite numeric H+ stage I included in the proposed Plan,
if Plan includes every positive E-free cut of a selected physical
original and every positive free cut of a root original, then an
omitted positive c is not the free cut of ANY actual stage original.
This includes the complete auxiliary parameter/meet source pool. -/
theorem finiteNumericH_stage_free_cut_not_omitted_of_plan_closed
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    (I Plan : Set Nat) (hIPlan : I ⊆ Plan)
    (hRootClosed : ∀ v : Fin N, v ∈ U →
      (finiteNumericH K k N).freeLevel v.val = 0 ∨
      (finiteNumericH K k N).freeLevel v.val ∈ Plan)
    (hPlanClosed : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH K k N).freeLevel v.val →
      (finiteNumericH K k N).freeLevel v.val ∈ Plan)
    (cut : Nat) (hCutPositive : 0 < cut)
    (hOmitted : cut ∉ Plan) :
    ∀ v : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N)
        (U : Set (Fin N)) I →
      (finiteNumericH K k N).freeLevel v.val ≠ cut := by
  intro v hv hEq
  rcases hv with hRoot | ⟨hSelected,hPositive⟩
  · obtain hZero | hInPlan :=
      hRootClosed v (Finset.mem_coe.mp hRoot)
    · omega
    · rw [hEq] at hInPlan
      exact hOmitted hInPlan
  · have hInPlan : (finiteNumericH K k N).freeLevel v.val ∈ Plan :=
      hPlanClosed v (hIPlan hSelected) hPositive
    rw [hEq] at hInPlan
    exact hOmitted hInPlan

/-- The genuine initial top-generation seed family (one root Kpt
original plus its actual TOP even-real ancestors) has NO ODD
terminal at a cut strictly below the root free E level.
Unlike lower-real seed absence this needs no generation bound. -/
theorem numericHTopGenerationSeeds_noOddBelowRoot
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (root : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel root.val)
    (a : Nat)
    (hBelow : 2*a+1 < (finiteNumericH K k N).freeLevel root.val) :
    ∀ z : AdmissibleKptNode family,
      z ∈ numericHTopGenerationSeeds
        family K k N hAvoid root blocks hWithin →
      LevelTree.lev z ≠ 2*a+1 := by
  intro z hz hLev
  obtain hRoot | ⟨i,hPrefix⟩ :=
    numericHTopGenerationSeeds_cases
      family K k N hAvoid root blocks hWithin z hz
  · rw [hRoot] at hLev
    change (finiteNumericH K k N).freeLevel root.val =
      2*a+1 at hLev
    omega
  · rw [hPrefix] at hLev
    have hLevTop :
        LevelTree.lev
          (LevelTree.ancestor
            ((finiteNumericH K k N).kptOriginal family hAvoid root)
            (hPosition k i.val k) (hWithin i.val i.property)) =
          hPosition k i.val k := LevelTree.level_ancestor _ _ _
    rw [hLevTop] at hLev
    obtain ⟨t,hEven⟩ := hPosition_even k i.val k
    omega

/-- Actual odd-cut nonselection from Plan's POSITIVE physical free
cut closure, a genuine descending stage inclusion and absence of
a seed at the odd cut. This is a conditional one-level result:
the Plan closure property is NOT derived from the resolved diary
and no assertion that Run.I 0 equals Plan is made. -/
theorem henson_actualRun_odd_omitted_of_closed_plan
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
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (a : Nat) (hBelow : 2*a+1 < top) (hCut : 2*a+1 < N)
    (Plan : Set Nat)
    (hAbove : Run.I ((2*a+1)+1) ⊆ Plan)
    (hRootClosed : ∀ v : Fin N, v ∈ U →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val = 0 ∨
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val ∈ Plan)
    (hPlanClosed : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val ∈ Plan)
    (hOmitted : 2*a+1 ∉ Plan)
    (hNoSeed : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = 2*a+1) :
    2*a+1 ∉ Run.I 0 := by
  have hNoStage :
      ∀ v : Fin N,
        v ∈ ambientStagePool
          (finiteNumericH (normalizedGraphModel E) k N)
          (U : Set (Fin N)) (Run.I ((2*a+1)+1)) →
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val
          ≠ 2*a+1 :=
    finiteNumericH_stage_free_cut_not_omitted_of_plan_closed
      (normalizedGraphModel E) k N U
      (Run.I ((2*a+1)+1)) Plan hAbove
      hRootClosed hPlanClosed
      (2*a+1) (by omega) hOmitted
  exact henson_actualRun_odd_unselected_of_no_seed_or_stage_free
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTop a hBelow hCut hNoSeed hNoStage

#print axioms Kk.finiteNumericH_stage_free_cut_not_omitted_of_plan_closed
#print axioms Kk.numericHTopGenerationSeeds_noOddBelowRoot
#print axioms Kk.henson_actualRun_odd_omitted_of_closed_plan

end Kk
