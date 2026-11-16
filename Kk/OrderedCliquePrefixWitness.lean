import Kk.FullRealGenerationCapacity
import Mathlib.Tactic

/-!
# Track A: increasing original clique prefix from attained clique capacity

English proof and adversarial audit committed BEFORE Lean:
  docs/ordered_clique_prefix_witness_english_audit.md

For a finite original set S strictly before b, all of whose
members are positively adjacent to b in the directed original
E table, and any a<=cap_E(S), choose an actual maximum original
E clique C⊆S and enumerate its first a elements in the given
NATURAL original order. Append b to obtain an increasing
(a+1)-vertex original E clique as a total Nat→Nat map q.

This is the missing abstract sorted-clique extraction used by
the independently stated physical partial numerical-H
staircase witness; it has no H generations, dependent Kpt
E/B3 or global Ramsey assumption.
-/

namespace Kk

/-- From a capacity-attaining genuine E clique in S,
choose its first a original names in increasing Nat order and
append b. We require the TRUE original E links to b and the
strict order of all members of S, not an abstract reindexing.

Even when a=0, the resulting total map has q(0)=b and all
index-restricted hypotheses hold vacuously. -/
theorem finiteDirectedCliqueCapacity_increasing_prefix_append
    (E : Nat → Nat → Bool) (S : Finset Nat)
    (b a : Nat)
    (hBefore : ∀ i ∈ S, i < b)
    (hLink : ∀ i ∈ S, E i b = true)
    (ha : a ≤ finiteDirectedCliqueCapacity E S) :
    ∃ q : Nat → Nat,
      q a = b ∧
      (∀ i, i < a → q i ∈ S) ∧
      (∀ i j, i < j → j < a+1 → q i < q j) ∧
      (∀ i j, i < j → j < a+1 →
        E (q i) (q j) = true) := by
  classical
  obtain ⟨C,hCSub,hClique,hCcard⟩ :=
    finiteDirectedCliqueCapacity_attained E S
  have haC : a ≤ C.card := by omega
  let f : Fin C.card ↪o Nat := C.orderEmbOfFin rfl
  let q : Nat → Nat := fun i =>
    if hi : i < a then
      f ⟨i,lt_of_lt_of_le hi haC⟩
    else b
  have hPrefix (i : Nat) (hi : i < a) :
      q i = f ⟨i,lt_of_lt_of_le hi haC⟩ := by
    simp [q,hi]
  have hLast : q a = b := by
    simp [q]
  have hCVal (i : Nat) (hi : i < a) :
      q i ∈ C := by
    rw [hPrefix i hi]
    exact C.orderEmbOfFin_mem rfl
      ⟨i,lt_of_lt_of_le hi haC⟩
  have hSVal (i : Nat) (hi : i < a) :
      q i ∈ S := hCSub (hCVal i hi)
  have hOrdered :
      ∀ i j, i < j → j < a+1 → q i < q j := by
    intro i j hij hj
    by_cases hja : j < a
    · have hia : i < a := lt_trans hij hja
      rw [hPrefix i hia,hPrefix j hja]
      apply f.strictMono
      exact (show
        (⟨i,lt_of_lt_of_le hia haC⟩ : Fin C.card) <
          (⟨j,lt_of_lt_of_le hja haC⟩ : Fin C.card)
        from by simpa using hij)
    · have hjeq : j = a := by omega
      subst j
      have hia : i < a := by omega
      rw [hLast]
      exact hBefore (q i) (hSVal i hia)
  refine ⟨q,hLast,hSVal,hOrdered,?_⟩
  intro i j hij hj
  by_cases hja : j < a
  · have hia : i < a := lt_trans hij hja
    exact hClique (q i) (hCVal i hia)
      (q j) (hCVal j hja)
      (ne_of_lt (hOrdered i j hij hj))
  · have hjeq : j = a := by omega
    subst j
    have hia : i < a := by omega
    rw [hLast]
    exact hLink (q i) (hSVal i hia)

#print axioms Kk.finiteDirectedCliqueCapacity_increasing_prefix_append

end Kk
