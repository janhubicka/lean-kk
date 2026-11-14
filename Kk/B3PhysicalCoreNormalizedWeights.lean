import Kk.IntegerWitnessCompleteComponent
import Mathlib.Tactic

/-!
# Track D: one physical forbidden clique has one normalized SORT-count vector

The extra input is an EXPLICIT type/sort map tau on clique indices.
It may include auxiliary parameter sorts, and need not be
injective. No selected-macrodiary source map or relative graph-age
feasibility theorem is inferred.

A forbidden K_ell through the tested cut has <= ell-1 upper
clique vertices. Sort-fibre counting turns its upper vertex
multiplicities into ONE normalized IntegerCliqueWeights vector
recording the cardinality on EVERY admissible support.

English proof + 14 hostile checks preceded this implementation:
docs/audits/2026-11-14-track-d-normalized-physical-clique-weights-english.md
-/

namespace Kk

/-- One complete forbidden-clique index set through a tested cut
can be normalized to a legitimate integer clique multiplicity
vector as soon as a sort label of EACH clique vertex is supplied.

The very SAME normalized vector records the cardinality of
cut-ABOVE clique vertices whose sorts lie in EVERY support T.

This only normalizes an EXPLICIT labelling tau. It does not
derive tau from the selected active macrodiary, and it does not
show feasibility/loss for any chosen integer graph-age function. -/
theorem physical_clique_upper_indices_have_normalized_sort_weights
    (d ell cut : Nat)
    (e : Fin ell → Nat)
    (tau : Fin ell → Fin d)
    (hAt : ∃ a : Fin ell, e a = cut) :
    ∃ w : IntegerCliqueWeights d ell,
      ∀ T : IntegerGraphSupport d ell,
        integerCliqueOnSupport w T =
          ((Finset.univ : Finset (Fin ell)).filter
            (fun a => cut < e a ∧ tau a ∈ T.1)).card := by
  classical
  obtain ⟨a0,ha0⟩ := hAt
  let upper : Finset (Fin ell) :=
    Finset.univ.filter (fun a => cut < e a)
  have hNot : a0 ∉ upper := by
    simp [upper,ha0]
  have hSub :
      upper ⊆ (Finset.univ : Finset (Fin ell)).erase a0 := by
    intro a ha
    have hNe : a ≠ a0 := by
      intro hEq
      subst a
      exact hNot ha
    exact Finset.mem_erase.mpr ⟨hNe,Finset.mem_univ _⟩
  have hUpperBound : upper.card ≤ ell-1 := by
    have h := Finset.card_le_card hSub
    simpa using h
  let count (j : Fin d) : Nat :=
    (upper.filter (fun a => tau a = j)).card
  have hCountBound (j : Fin d) : count j < ell := by
    have hSubCount :
        (upper.filter (fun a => tau a = j)).card ≤ upper.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hPos : 0 < ell := by omega
    dsimp [count]
    omega
  let v : Fin d → Fin ell :=
    fun j => ⟨count j,hCountBound j⟩
  have hFibre (T : Finset (Fin d)) :
      (upper.filter (fun a => tau a ∈ T)).card =
        ∑ j ∈ T, count j := by
    have hPartition := Finset.sum_card_fiberwise_eq_card_filter
      (s := upper) T tau
    simpa only [count] using hPartition.symm
  have hCountTotal :
      (Finset.univ : Finset (Fin d)).sum count = upper.card := by
    have h := hFibre (Finset.univ : Finset (Fin d))
    simpa using h.symm
  let w : IntegerCliqueWeights d ell :=
    ⟨v,by
      change (Finset.univ : Finset (Fin d)).sum count ≤ ell-1
      rw [hCountTotal]
      exact hUpperBound⟩
  refine ⟨w,?_⟩
  intro T
  change T.1.sum count =
    ((Finset.univ : Finset (Fin ell)).filter
      (fun a => cut < e a ∧ tau a ∈ T.1)).card
  rw [←hFibre T.1]
  simp only [upper,Finset.filter_filter]
  congr 1
  ext a
  simp [and_comm,and_left_comm,and_assoc]

#print axioms physical_clique_upper_indices_have_normalized_sort_weights

end Kk
