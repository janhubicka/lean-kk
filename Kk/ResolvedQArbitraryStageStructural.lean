import Kk.GenerationZeroStageCoherence
import Kk.PositiveGenerationStructural
import Mathlib.Tactic

/-! Structural lift for arbitrary J ⊆ Plan, including forced-retained stages. -/
namespace Kk
open SuccessorTree
open SuccessorTree.V10

theorem resolvedQ_arbitrary_stage_generation_zero_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (J : Set Nat)
    (b : Nat) (hk : 0 < k) (hPositive : 0 < hPosition k b 0)
    (hCut : hPosition k b 0 < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b 0)
    (Plan : Set Nat)
    (hAbove : J ⊆ Plan)
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
    (hBlockInterval : ∀ p b j block : Nat, ∀ a d : Bool,
      p < b → b < j → role p = .auxiliary block a →
      role j = .auxiliary block d →
      role b = .dummy ∨ ∃ f : Bool, role b = .auxiliary block f)
    (hOmitted : ResolvedQOmittedBase (role b))
    (hOldNeighbour : ∀ j : Nat, b < j → role j = .coded true →
      E b j = true → ∃ p : Nat, p < b ∧ E p j = true)
    (hNoSplit : ∀ j j' : Nat, b < j → b < j' →
      role j = .coded true → role j' = .coded true →
      (∀ p : Nat, p < b → E p j = E p j') → E b j = E b j') :
    let cut : Nat := hPosition k b 0
    let Z : Set (AdmissibleKptNode family) :=
      SMTree.Envelope.closure
        (admissibleKptSTree family) (J) X
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
    (J) b 0 hPositive hNoSeedAt
  intro v w hFreeV hFreeW hOld
  exact resolvedQ_generation_zero_stage_full_type_coherent
    E k N hk U J Plan hAbove role hQ hRootDummy hPlanShape hBlockInterval
    b hCut hOmitted hOldNeighbour hNoSplit v w hFreeV hFreeW hOld


theorem resolvedQ_arbitrary_stage_positive_generation_no_full_I1_I2
    (family : List (NormalizedForbidden 1 0 1))
    (E : Nat → Nat → Bool) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH (normalizedGraphModel E) k N).L)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH (normalizedGraphModel E) k N)
      hAvoid (U : Set (Fin N)))
    (J : Set Nat)
    (b g : Nat) (hg0 : 0 < g) (hg : g < k)
    (hCut : hPosition k b g < N)
    (hNoSeedAt : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ X ∧ LevelTree.lev z = hPosition k b g)
    (Plan : Set Nat)
    (hAbove : J ⊆ Plan)
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
        (admissibleKptSTree family) (J) X
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
    (J) b g hPositive hNoSeedAt
  intro v w hFreeV hFreeW hOld
  exact resolvedQ_positive_lower_generation_stage_full_type_coherent
    E k N U (J) Plan hAbove role hQ hRootDummy hPlanShape
    b g hg0 hg hCut hOmitted v w hFreeV hFreeW hOld


end Kk
