import Kk.PositiveGenerationStageCoherence
import Kk.StageCoherenceStructural
import Kk.TrackDTopSeedNoLowerReal
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# Actual positive-generation structural exclusion in resolved Q

English proof and independent reviews were published before this source:
`docs/stage_coherence_structural_lift_english_20261123.md`.

Complete coherence on the literal current-stage original pool gives both
full structural exclusions at an omitted base's positive lower generation.
The concrete TOP-generation seed family discharges source representation
and seed absence. The descending stage-Plan inclusion stays explicit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At the literal Run.I(cut+1) stage, positive lower generations of an
omitted resolved-Q base have no full I1 terminal and no full I2 meet, provided
the actual seeds are represented and no seed ends at the cut. Neither
structural verdict nor a chosen-age verdict is assumed. -/
theorem resolvedQ_actualRun_positive_lower_generation_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (b g : Nat) (hg0 : 0 < g) (hg : g < k)
    (hCut : hPosition k b g < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b g)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k b g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role b)) :
    let cut : Nat := hPosition k b g
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure
        (admissibleKptSTree family) (Run.I (cut+1)) X
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b' : AdmissibleKptNode family, b' ∈ Z ∧
        SMTree.Envelope.SameComponent a b' ∧
        LevelTree.lev (LevelTree.meet a b') = cut) := by
  classical
  intro cut Z
  have hPositive : 0 < cut := by
    dsimp [cut,hPosition]
    omega
  apply finiteNumericH_even_real_no_full_I1_I2_of_coherent_stage
    family (normalizedGraphModel E) k N hAvoid U X hX
    (Run.I (cut+1)) b g hPositive hNoSeedAt
  intro v w hFreeV hFreeW hOld
  exact resolvedQ_positive_lower_generation_stage_full_type_coherent
    E k N U (Run.I (cut+1)) Plan hAbove role hQ hRootDummy hPlanShape
    b g hg0 hg hCut hOmitted v w hFreeV hFreeW hOld

/-- For the literal cap original and its TOP-generation ancestor seeds,
source representation and seed absence are verified. Positive lower
generations of omitted resolved-Q bases therefore have no full I1 or I2
under the actual higher-stage Plan inclusion and bounded role contracts. -/
theorem resolvedQ_topSeeds_positive_lower_generation_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (cap : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family (normalizedGraphModel E)
        k N hAvoid cap blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH (normalizedGraphModel E) k N).freeLevel cap.val))
    (b g : Nat) (hg0 : 0 < g) (hg : g < k)
    (hCut : hPosition k b g < N)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k b g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ j m : Nat, m ≤ k →
      cap.val = hPosition k j m → role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role b)) :
    let X : Set (AdmissibleKptNode family) :=
      numericHTopGenerationSeeds family (normalizedGraphModel E)
        k N hAvoid cap blocks hWithin
    let cut : Nat := hPosition k b g
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure
        (admissibleKptSTree family) (Run.I (cut+1)) X
    (¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = cut) ∧
    (¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
      ∃ b' : AdmissibleKptNode family, b' ∈ Z ∧
        SMTree.Envelope.SameComponent a b' ∧
        LevelTree.lev (LevelTree.meet a b') = cut) := by
  classical
  let K : AgeTestModel 1 0 1 := normalizedGraphModel E
  let A : EnumeratedPartialStructure 1 0 1 := finiteNumericH K k N
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoid cap blocks hWithin
  let top : Nat := A.freeLevel cap.val
  let U : Finset (Fin N) := {cap}
  have hX : X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N)) := by
    simpa only [X,U,A,Finset.coe_singleton] using
      (numericHTopGenerationSeeds_subset_rootPool
        family K k N hAvoid cap blocks hWithin)
  have hPositive : 0 < hPosition k b g := by
    dsimp [hPosition]
    omega
  have hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b g := by
    rintro ⟨z,hz,hLevel⟩
    exact (numericHTopGenerationSeeds_noPositiveLowerReal
      family K k N hAvoid cap blocks hWithin
      b g hg hPositive z hz) hLevel
  have hRootDummy' : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy := by
    intro v hv j m hm hAddr
    have hvCap : v = cap := by simpa [U] using hv
    subst v
    exact hRootDummy j m hm hAddr
  exact resolvedQ_actualRun_positive_lower_generation_no_full_I1_I2
    family E k N hAvoid U X hX top Run b g hg0 hg hCut hNoSeedAt
    Plan hAbove role hQ hRootDummy' hPlanShape hOmitted


/-- A genuine positive lower-real AlgorithmRun cut at an omitted resolved-Q
base is skipped under the actual chosen Marked corrected-B3 verdict. Both
full structural exclusions are DERIVED from whole-stage coherence and seed
absence. The strict cut/top bound, top seed, Henson hypotheses, actual Plan
inclusion, and chosen age verdict remain explicit application inputs. -/
theorem henson_actualRun_positive_lower_real_unselected_of_planned_stage_markedB3
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
    (idx g : Nat) (hg0 : 0 < g) (hg : g < k)
    (hBelow : hPosition k idx g < top)
    (hCut : hPosition k idx g < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily ell hell),
      z ∈ X ∧ LevelTree.lev z = hPosition k idx g)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k idx g+1) ⊆ Plan)
    (role : Nat → ResolvedQBaseRole)
    (hQ : ResolvedQChronologicalAxioms role E)
    (hRootDummy : ∀ v : Fin N, v ∈ U →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        role j = .dummy)
    (hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
      0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
      ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
        (role j = .coded true ∧ m = k) ∨
        (∃ block : Nat, role j = .auxiliary block true))
    (hOmitted : ResolvedQOmittedBase (role idx)) :
    let cut : Nat := hPosition k idx g
    let Stage : Finset (Fin N) :=
      hStageOriginals (normalizedGraphModel E) k N U (Run.I (cut+1))
    let original : Fin Stage.card → Fin N := hOriginalName Stage
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily ell hell)) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily ell hell))
        (Run.I (cut+1)) X
    let Full : Fin Stage.card → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily ell hell)
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidA original Z cut
    let Marked : Fin Stage.card → Prop :=
      resolvedQStageSelectedTopMarked role k Stage Full
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Marked).CorrectedB3
        (hensonForbiddenFamily ell hell) →
    cut ∉ Run.I 0 := by
  classical
  intro cut Stage original Z Full Marked hMarkedB3
  have hPositive : 0 < cut := by
    dsimp [cut,hPosition]
    omega
  obtain ⟨hNoI1,hNoI2⟩ :=
    resolvedQ_actualRun_positive_lower_generation_no_full_I1_I2
      (hensonForbiddenFamily ell hell) E k N hAvoidA U X hX top Run
      idx g hg0 hg hCut hNoSeedAt
      Plan hAbove role hQ hRootDummy hPlanShape hOmitted
  exact henson_actualRun_lower_real_unselected_of_planned_stage_markedB3
    ell hell k hK E hLoops hSym hClique
    N U hAvoidA X hX top Run hTop
    idx g hg hPositive hBelow hCut hNoI1 hNoI2
    Plan hAbove role hQ hRootDummy hPlanShape hOmitted hMarkedB3

#print axioms Kk.resolvedQ_actualRun_positive_lower_generation_no_full_I1_I2
#print axioms Kk.resolvedQ_topSeeds_positive_lower_generation_no_full_I1_I2

#print axioms Kk.henson_actualRun_positive_lower_real_unselected_of_planned_stage_markedB3

end Kk
