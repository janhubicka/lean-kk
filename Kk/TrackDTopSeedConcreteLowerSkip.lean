import Kk.TrackDZeroStageActualRunSkip
import Kk.TrackDTopSeedNoLowerReal
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Track D: true top-generation cap seeds discharge seed and source gates

English-first proof, 16 adversarial checks, and November 20 exact-source
qualification were committed BEFORE this Lean file:
docs/audits/2026-11-20-track-d-concrete-topseed-skips-english.md

For the LITERAL numerical H+ seed family consisting of one cap full
Kpt original and its finite TOP-generation ancestors, the root-source
representation and seed-at-positive-lower-real absence are both
verified properties, not independent premises. These are composed
with the true AlgorithmRun no-I1/no-I2/no-I3 cut criterion.

The isolated-dummy cut needs no proposed Plan. The selected-coding
lower real cut needs only an actual higher-stage Plan inclusion and
the explicit chronological original-Q role/independence conditions.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At a finite genuine Henson AlgorithmRun whose source is the
literal root-cap top-generation Kpt seed family, every positive
lower-real cut of an ISOLATED old-Q base is skipped. No independent
seed-at-cut, no-I1, no-I2, corrected B3 or Plan assumption remains. -/
theorem henson_topSeeds_isolated_dummy_lower_real_skip
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
    (cap : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell))
      (numericHTopGenerationSeeds
        (hensonForbiddenFamily ell hell) (normalizedGraphModel E)
        k N hAvoid cap blocks hWithin :
          Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val))
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g <
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (hCut : hPosition k idx g < N)
    (hIsolated : ∀ j : Nat, E idx j = false) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoid cap blocks hWithin
  let top : Nat := A.freeLevel cap.val
  let U : Finset (Fin N) := {cap}
  have hX :
      X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N)) := by
    exact numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoid cap blocks hWithin
  have hRootIn : A.kptOriginal family hAvoid cap ∈ X := by
    simp [X, numericHTopGenerationSeeds, A]
  have hTopSeed : ∃ x ∈ X, LevelTree.lev x = top := by
    refine ⟨A.kptOriginal family hAvoid cap,hRootIn,?_⟩
    rfl
  have hNoSeed :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ X ∧ LevelTree.lev z = hPosition k idx g := by
    rintro ⟨z,hz,hLevel⟩
    exact (numericHTopGenerationSeeds_noPositiveLowerReal
      family K k N hAvoid cap blocks hWithin
      idx g hg hPos z hz) hLevel
  exact henson_actualRun_isolated_dummy_lower_real_skip_of_no_seed
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTopSeed
    idx g hg hPos hBelow hCut hNoSeed hIsolated

/-- For the SAME concrete true root-cap Kpt top-generation source,
an omitted lower generation of an independent selected coded Q base
is skipped under the GENUINE descending actual-stage inclusion
Run.I(cut+1) subset Plan and the literal retained block role axioms.
Neither full I1/I2 nor the chosen B3 nor seed-at-cut is assumed. -/
theorem henson_topSeeds_selected_coded_lower_real_skip
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
    (cap : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell))
      (numericHTopGenerationSeeds
        (hensonForbiddenFamily ell hell) (normalizedGraphModel E)
        k N hAvoid cap blocks hWithin :
          Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val))
    (idx g : Nat) (hg : g < k)
    (hPos : 0 < hPosition k idx g)
    (hBelow : hPosition k idx g <
      (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (hCut : hPosition k idx g < N)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k idx g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hIndependent : ∀ i j,
      role i = .coded true →
      role j = .coded true → E i j = false)
    (hRootDummy : ∀ j m : Nat,
      cap.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hSelectedBase : role idx = .coded true) :
    hPosition k idx g ∉ Run.I 0 := by
  classical
  let family := hensonForbiddenFamily ell hell
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoid cap blocks hWithin
  let top : Nat := A.freeLevel cap.val
  let U : Finset (Fin N) := {cap}
  have hX :
      X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoid cap blocks hWithin
  have hRootIn : A.kptOriginal family hAvoid cap ∈ X := by
    simp [X, numericHTopGenerationSeeds, A]
  have hTopSeed : ∃ x ∈ X, LevelTree.lev x = top := by
    refine ⟨A.kptOriginal family hAvoid cap,hRootIn,?_⟩
    rfl
  have hNoSeed :
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ X ∧ LevelTree.lev z = hPosition k idx g := by
    rintro ⟨z,hz,hLevel⟩
    exact (numericHTopGenerationSeeds_noPositiveLowerReal
      family K k N hAvoid cap blocks hWithin
      idx g hg hPos z hz) hLevel
  have hRootDummy' : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, v.val = hPosition k j m →
        role j = .dummy := by
    intro v hv j m hAddr
    have hvCap : v = cap := by simpa [U] using hv
    subst v
    exact hRootDummy j m hAddr
  exact henson_actualRun_selected_coded_lower_real_skip_of_no_seed
    ell hell k hK E hLoops hSym hClique
    N U hAvoid X hX top Run hTopSeed
    idx g hg hPos hBelow hCut hNoSeed
    Plan hAbove role hQ hIndependent
    hRootDummy' hPlanShape hSelectedBase

#print axioms Kk.henson_topSeeds_isolated_dummy_lower_real_skip
#print axioms Kk.henson_topSeeds_selected_coded_lower_real_skip

end Kk
