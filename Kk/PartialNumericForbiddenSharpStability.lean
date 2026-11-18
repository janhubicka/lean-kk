import Kk.PartialNumericLateAgeStability
import Kk.FiniteOldColumnAge
import Mathlib.Tactic

/-!
# Track A: sharply bounded support events under actual finite clique-freeness

English proof and hostile audit:
  docs/track_a_forbidden_sharp_partial_stability_english_audit_20261118.md

This module uses an actual finite forbidden-clique certificate at the
relevant original pool, not an invented abstract graph-age assumption.
A bridge from Henson's normalized hensonForbiddenFamily avoidance
to that certificate is a separate forthcoming integration lemma.
No dependent Kpt E/B3 or global BRD claim.
-/

namespace Kk

open SuccessorTree.V10

/-- A finite set S of original vertices all before b, linked to b
and to one later vertex t, with b linked to t, has capacity at most
ell-3 when the actual pool S ∪ {b,t} is K_ell-free.
This is a finite *actual graph* argument, not arithmetic on raw ages. -/
theorem trackA_linked_clique_capacity_two_vertex_budget
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell b t : Nat) (S : Finset Nat)
    (hBefore : ∀ x ∈ S, x < b)
    (hbt : b < t)
    (hLinkB : ∀ x ∈ S, E x b = true)
    (hLinkT : ∀ x ∈ S, E x t = true)
    (hBtEdge : E b t = true)
    (hFree : finitePoolCliqueCheck E ell
      (insert t (insert b S)) = false) :
    finiteDirectedCliqueCapacity E S + 2 < ell := by
  classical
  obtain ⟨C,hSub,hClique,hCard⟩ :=
    finiteDirectedCliqueCapacity_attained E S
  have hbNot : b ∉ C := by
    intro hb
    exact (Nat.lt_irrefl b) (hBefore b (hSub hb))
  have htNot : t ∉ C := by
    intro ht
    have h := hBefore t (hSub ht)
    omega
  have hBt : b ≠ t := ne_of_lt hbt
  let D : Finset Nat := insert t (insert b C)
  have hSubD : D ⊆ insert t (insert b S) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hSub hx))
  have hCliqueD : IsDirectedCliqueOn E D := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxT | hx
    · subst x
      rcases Finset.mem_insert.mp hy with hyT | hy
      · exact False.elim (hxy hyT.symm)
      · rcases Finset.mem_insert.mp hy with hyB | hyC
        · subst y
          simpa [hSym b t] using hBtEdge
        · exact (hSym y t).symm.trans (hLinkT y (hSub hyC))
    · rcases Finset.mem_insert.mp hx with hxB | hxC
      · subst x
        rcases Finset.mem_insert.mp hy with hyT | hy
        · subst y
          exact hBtEdge
        · rcases Finset.mem_insert.mp hy with hyB | hyC
          · exact False.elim (hxy hyB.symm)
          · exact (hSym y b).symm.trans (hLinkB y (hSub hyC))
      · rcases Finset.mem_insert.mp hy with hyT | hy
        · subst y
          exact hLinkT x (hSub hxC)
        · rcases Finset.mem_insert.mp hy with hyB | hyC
          · subst y
            exact hLinkB x (hSub hxC)
          · exact hClique x hxC y hyC hxy
  have hCardD : D.card = C.card + 2 := by
    dsimp [D]
    rw [Finset.card_insert_of_not_mem]
    · rw [Finset.card_insert_of_not_mem hbNot]
      omega
    · simp [htNot, hBt.symm]
  have hCapacity :=
    directedClique_card_le_capacity E
      (insert t (insert b S)) D hSubD hCliqueD
  have hFreeCapacity :=
    (finitePoolCliqueCheck_false_iff_capacity_lt E ell
      (insert t (insert b S))).mp hFree
  omega

/-- Exact source-local criterion: if every eligible equal-capacity
support has a genuine finite K_ell-free two-vertex original pool,
ordinary-L raw age is constant after generation ell-2.
This is the sharp forbidden-graph specialization of general ell-1
stability, and avoids silently assuming a Kpt/B3 identification. -/
theorem trackA_partial_raw_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    finiteNumericHPartialActualRawAt E ell k b h M j =
      finiteNumericHPartialActualRawAt E ell k b g M j := by
  classical
  funext U
  have hMono :
      finiteNumericHPartialActualRawAt E ell k b h M j U ≤
        finiteNumericHPartialActualRawAt E ell k b g M j U :=
    finiteNumericH_partial_actual_raw_age_antitone
      E ell k b M g h hgh j U
  by_contra hNe
  have hStrict :
      finiteNumericHPartialActualRawAt E ell k b h M j U <
        finiteNumericHPartialActualRawAt E ell k b g M j U := by
    omega
  obtain ⟨hEligible,hCapacity,hCut,_,_⟩ :=
    (finiteNumericH_partial_actual_raw_support_event_iff
      E hSym ell k b g h M hgh hh j hj U).mp hStrict
  obtain ⟨t, ht⟩ := U.2.1
  let P : Finset Nat :=
    oldSupportCommonNeighbourPool (Finset.range b)
      (fun i z => E i (j z)) U.1
  let S : Finset Nat := P.filter (fun i => E i b = true)
  have hBefore : ∀ x ∈ S, x < b := by
    intro x hx
    exact Finset.mem_range.mp
      (Finset.mem_filter.mp
        ((Finset.mem_filter.mp hx).1)).1
  have hLinkB : ∀ x ∈ S, E x b = true := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hLinkT : ∀ x ∈ S, E x (j t) = true := by
    intro x hx
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp hx).1)).2 t ht
  have hFree : finitePoolCliqueCheck E ell
      (insert (j t) (insert b S)) = false :=
    hPoolsFree U t ht
  have hBound := trackA_linked_clique_capacity_two_vertex_budget
    E hSym ell b (j t) S hBefore (hj t)
    hLinkB hLinkT (hEligible t ht) hFree
  change finiteDirectedCliqueCapacity E S =
    finiteDirectedCliqueCapacity E P at hCapacity
  omega

/-- Canonical ordinary-L ages inherit the sharp source-local
stability by rewriting the whole raw support function. -/
theorem trackA_partial_canonical_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    integerGraphAgeCanonical d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_partial_raw_stable_of_two_vertex_free
    E hSym ell k b g h M hLate hgh hh j hj hPoolsFree]

/-- Feasible normalized integer clique vectors also stabilize. -/
theorem trackA_partial_feasible_stable_of_two_vertex_free
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (ell k b g h M : Nat)
    (hLate : ell - 2 ≤ g) (hgh : g ≤ h) (hh : h ≤ k)
    (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (hPoolsFree : ∀ (U : IntegerGraphSupport d ell)
      (t : Fin d), t ∈ U.1 →
      finitePoolCliqueCheck E ell
        (insert (j t)
          (insert b
            ((oldSupportCommonNeighbourPool (Finset.range b)
              (fun i z => E i (j z)) U.1).filter
                (fun i => E i b = true)))) = false) :
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b h M j) =
    feasibleIntegerCliqueVectors d ell
      (finiteNumericHPartialActualRawAt E ell k b g M j) := by
  rw [trackA_partial_raw_stable_of_two_vertex_free
    E hSym ell k b g h M hLate hgh hh j hj hPoolsFree]

#print axioms Kk.trackA_linked_clique_capacity_two_vertex_budget
#print axioms Kk.trackA_partial_raw_stable_of_two_vertex_free
#print axioms Kk.trackA_partial_canonical_stable_of_two_vertex_free
#print axioms Kk.trackA_partial_feasible_stable_of_two_vertex_free

end Kk
