import Kk.TrackDResolvedQBaseRoles
import SuccessorTree.V10.HExactE
import Mathlib.Tactic

/-!
# Canonical-generation regression for real numerical-H addresses

The English-first interface audit is
`docs/bounded_stage_roles_repair_english_20261123.md`.

An unbounded generation argument aliases an earlier base. The bounded
root and Plan contracts admit the intended concrete roles below, while
their unbounded versions would impose contradictory roles. These are
regressions for application hypotheses, not counterexamples to any
previous theorem under its stated assumptions.
-/

namespace Kk

open SuccessorTree.V10

/-- The first out-of-range generation is the next base's generation zero. -/
theorem hPosition_generation_overflow_alias (k j : Nat) :
    hPosition k (j+1) 0 = hPosition k j (k+1) := by
  simp only [hPosition]
  ring

/-- A genuine TOP address also has an unbounded earlier-base presentation. -/
theorem hPosition_top_generation_overflow_alias (k j : Nat) :
    hPosition k (j+1) k = hPosition k j (2*k+1) := by
  simp only [hPosition]
  ring

/-- A dummy TOP cap at address 16 coexists with the selected earlier base 1
under the bounded root contract. The old unbounded root contract would
force that selected base dummy via its generation-5 alias. -/
theorem resolvedQ_bounded_root_contract_alias_regression :
    let role : Nat → ResolvedQBaseRole :=
      fun j => if j = 1 then .coded true else .dummy
    role 1 = .coded true ∧ role 2 = .dummy ∧
      (∀ j m : Nat, m ≤ 2 → 16 = hPosition 2 j m → role j = .dummy) ∧
      ¬ (∀ j m : Nat, 16 = hPosition 2 j m → role j = .dummy) := by
  intro role
  refine ⟨by simp [role], by simp [role], ?_, ?_⟩
  · intro j m hm hAddress
    have hEqual : hPosition 2 2 2 = hPosition 2 j m := by
      change 16 = hPosition 2 j m
      exact hAddress
    obtain ⟨hBase,_hGeneration⟩ :=
      hPosition_injective_bounded 2 2 2 j m (by decide) hm hEqual
    rw [← hBase]
    simp [role]
  · intro hUnbounded
    have hContradiction := hUnbounded 1 5 (by norm_num [hPosition])
    simp [role] at hContradiction

/-- A selected TOP Plan address 10 coexists with an initial dummy base 0
under bounded decoding. Unbounded decoding would require base 0 to be
selected coding or retained auxiliary through the generation-5 alias. -/
theorem resolvedQ_bounded_plan_contract_alias_regression :
    let role : Nat → ResolvedQBaseRole :=
      fun j => if j = 1 then .coded true else .dummy
    role 0 = .dummy ∧
      (∀ j m : Nat, m ≤ 2 → 10 = hPosition 2 j m →
        (role j = .coded true ∧ m = 2) ∨
        ∃ block : Nat, role j = .auxiliary block true) ∧
      ¬ (∀ j m : Nat, 10 = hPosition 2 j m →
        (role j = .coded true ∧ m = 2) ∨
        ∃ block : Nat, role j = .auxiliary block true) := by
  intro role
  refine ⟨by simp [role], ?_, ?_⟩
  · intro j m hm hAddress
    have hEqual : hPosition 2 1 2 = hPosition 2 j m := by
      change 10 = hPosition 2 j m
      exact hAddress
    obtain ⟨hBase,hGeneration⟩ :=
      hPosition_injective_bounded 2 1 2 j m (by decide) hm hEqual
    subst j
    subst m
    exact Or.inl ⟨by simp [role], rfl⟩
  · intro hUnbounded
    have hContradiction := hUnbounded 0 5 (by norm_num [hPosition])
    simp [role] at hContradiction

#print axioms Kk.hPosition_generation_overflow_alias
#print axioms Kk.hPosition_top_generation_overflow_alias
#print axioms Kk.resolvedQ_bounded_root_contract_alias_regression
#print axioms Kk.resolvedQ_bounded_plan_contract_alias_regression

end Kk
