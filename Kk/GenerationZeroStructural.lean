import Kk.GenerationZeroStageCoherence
import Kk.StageCoherenceStructural
import Mathlib.Tactic

/-!
# Generation-zero structural exclusion for an actual represented seed family

English proof and independent review precede this source in
`docs/generation_zero_stage_coherence_english_20261124.md` and
`docs/audits/2026-11-24-generation-zero-coherence-independent-review.md`.

The seeds may be any genuinely represented family, including the enlarged
family of all planned cap ancestors. Only absence of a seed at the tested
cut is required; this is not a theorem restricted to the smaller TOP seed
family. Whole-stage generation-zero coherence derives both no-I1 and no-I2.
The K4 singleton-neutrality and ordinary no-split construction properties,
the actual descending Plan inclusion, and the chosen B3 verdict stay explicit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- At the true Run.I(cut+1) stage, an omitted non-dummy generation-zero
cut has neither a full I1 endpoint nor a full I2 meet. Complete structural
exclusion is derived from the ordinary construction properties; the seeds
are arbitrary actual represented originals and their prefixes. -/
theorem resolvedQ_actualRun_zero_generation_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat) (hk : 0 < k)
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
    (b : Nat) (hPos : 0 < hPosition k b 0)
    (hCut : hPosition k b 0 < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b 0)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k b 0+1) ⊆ Plan)
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
    (hBlockInterval :
      ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
        p < b → b < j →
        role p = .auxiliary block pastFlag →
        role j = .auxiliary block futureFlag →
        role b = .dummy ∨
          ∃ middleFlag : Bool, role b = .auxiliary block middleFlag)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hNonDummy : role b ≠ .dummy)
    (hNoSplit : ResolvedQSelectedNoSplitAt role E b)
    (hNeutral : ResolvedQK4SingletonNeutralAt role E b) :
    let cut : Nat := hPosition k b 0
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
  apply finiteNumericH_even_real_no_full_I1_I2_of_coherent_stage
    family (normalizedGraphModel E) k N hAvoid U X hX
    (Run.I (cut+1)) b 0 hPos hNoSeedAt
  intro v w hFreeV hFreeW hOld
  exact resolvedQ_zero_generation_stage_full_type_coherent
    E k N hk U (Run.I (cut+1)) Plan hAbove role hQ
    hRootDummy hPlanShape hBlockInterval b hCut hOmitted hNonDummy
    hNoSplit hNeutral v w hFreeV hFreeW hOld

/-- A K4-free actual run skips an omitted positive generation-zero cut
under its chosen marked corrected-B3 verdict. Both full structural gates
are derived from the concrete singleton neutrality and selected no-split
properties on the whole represented stage. General represented seeds are
allowed, so planned cap ancestors are not excluded by the statement. -/
theorem k4_actualRun_zero_generation_unselected_of_planned_stage_markedB3
    (k : Nat) (hK : 4 ≤ k+1)
    (E : Nat → Nat → Bool)
    (hLoops : ∀ i, E i i = false)
    (hSym : ∀ x y, E x y = E y x)
    (hClique : ¬ ∃ f : Fin 4 → Nat, StrictMono f ∧
      (∀ a b : Fin 4, a ≠ b → E (f a) (f b) = true))
    (N : Nat)
    (U : Finset (Fin N))
    (hAvoidA : ∀ bad, bad ∈ hensonForbiddenFamily 4 (of_decide_eq_true rfl) →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (of_decide_eq_true rfl))))
    (hX : X ⊆ ambientPrefixPool
      (hensonForbiddenFamily 4 (of_decide_eq_true rfl))
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoidA (U : Set (Fin N)))
    (top : Nat)
    (Run : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl))) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (b : Nat) (hPos : 0 < hPosition k b 0)
    (hBelow : hPosition k b 0 < top)
    (hCut : hPosition k b 0 < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode
      (hensonForbiddenFamily 4 (of_decide_eq_true rfl)),
      z ∈ X ∧ LevelTree.lev z = hPosition k b 0)
    (Plan : Set Nat)
    (hAbove : Run.I (hPosition k b 0+1) ⊆ Plan)
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
    (hBlockInterval :
      ∀ p b j block : Nat, ∀ pastFlag futureFlag : Bool,
        p < b → b < j →
        role p = .auxiliary block pastFlag →
        role j = .auxiliary block futureFlag →
        role b = .dummy ∨
          ∃ middleFlag : Bool, role b = .auxiliary block middleFlag)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hNonDummy : role b ≠ .dummy)
    (hNoSplit : ResolvedQSelectedNoSplitAt role E b)
    (hNeutral : ResolvedQK4SingletonNeutralAt role E b) :
    let cut : Nat := hPosition k b 0
    let Stage : Finset (Fin N) :=
      hStageOriginals (normalizedGraphModel E) k N U (Run.I (cut+1))
    let original : Fin Stage.card → Fin N := hOriginalName Stage
    let Z : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (of_decide_eq_true rfl))) :=
      SMTree.Envelope.closure
        (admissibleKptSTree (hensonForbiddenFamily 4 (of_decide_eq_true rfl)))
        (Run.I (cut+1)) X
    let Full : Fin Stage.card → Prop :=
      closureSelectedOriginal (hensonForbiddenFamily 4 (of_decide_eq_true rfl))
        (finiteNumericH (normalizedGraphModel E) k N)
        hAvoidA original Z cut
    let Marked : Fin Stage.card → Prop :=
      resolvedQStageSelectedTopMarked role k Stage Full
    (selectedStagePoolPrescribedData
      (finiteNumericH (normalizedGraphModel E) k N)
      cut original Marked).CorrectedB3
        (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) →
    cut ∉ Run.I 0 := by
  classical
  intro cut Stage original Z Full Marked hMarkedB3
  have hk : 0 < k := by omega
  obtain ⟨hNoI1,hNoI2⟩ :=
    resolvedQ_actualRun_zero_generation_no_full_I1_I2
      (hensonForbiddenFamily 4 (of_decide_eq_true rfl)) E k N hk hAvoidA U X hX
      top Run b hPos hCut hNoSeedAt Plan hAbove role hQ
      hRootDummy hPlanShape hBlockInterval hOmitted hNonDummy hNoSplit hNeutral
  exact henson_actualRun_lower_real_unselected_of_planned_stage_markedB3
    4 (of_decide_eq_true rfl) k hK E hLoops hSym hClique N U hAvoidA X hX
    top Run hTop b 0 hk hPos hBelow hCut hNoI1 hNoI2
    Plan hAbove role hQ hRootDummy hPlanShape hOmitted hMarkedB3

#print axioms Kk.resolvedQ_actualRun_zero_generation_no_full_I1_I2
#print axioms Kk.k4_actualRun_zero_generation_unselected_of_planned_stage_markedB3

end Kk
