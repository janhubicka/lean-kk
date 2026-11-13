import Kk.FiniteInducedOnePointExtension
import Kk.FiniteNeighbourSchedule
import Mathlib.Tactic

/-!
# Chronological induced embedding of any finite K_ell-free L-graph

English proof and hostile review committed BEFORE this file:
  docs/finite_chronological_henson_embedding_english_audit.md

The target A is a symmetric loop-free finite Boolean L pattern on [0,N).
The fixed countable E has all prefixes K_ell-free and OnePointLeftDense.
Recursively embed the earlier pattern, certify the COMPLETE abstract
old-neighbour S for the next vertex, transfer its sharp clique safety to
the true induced image, and apply the physical one-point theorem.
The new original may lie beyond the chosen front; all positive edges
to intervening unnamed old indices are excluded by that theorem.

This proves finite ordinary-L universality under the stated fixed
enumeration assumptions, not the entire numerical-H+ resolved diary,
auxiliary Kpt E/parameter-closed B3 or a common labelled source orbit.
-/

namespace Kk

/-- Exact strictly increasing induced embedding of the first N vertices
of an arbitrary finite symmetric loop-free K_ell-free target pattern
into the genuine fixed left-dense E enumeration. Strict monotonicity
and complete directed L atom agreement are required only on [0,N).

The induction uses real later indices and every-stage complete
old-neighbour K_(ell-1)-freeness; this does not claim that the E graph
on omitted gap indices is isomorphic to the target A. -/
theorem onePointLeftDense_embeds_finite_KFree_pattern
    (A E : Nat → Nat → Bool) (ell N : Nat)
    (hell : 0 < ell)
    (hASym : ∀ i j, A i j = A j i)
    (hALoops : ∀ i, A i i = false)
    (hDense : OnePointLeftDense E ell)
    (hEFree : ∀ front, ¬ HasCliqueBelow E front ell)
    (hAFree : ¬ HasCliqueBelow A N ell) :
    ∃ f : Nat → Nat,
      (∀ i j : Nat, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j : Nat, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) := by
  classical
  have construct (n : Nat) :
      ¬ HasCliqueBelow A n ell →
      ∃ f : Nat → Nat,
        (∀ i j : Nat, i < n → j < n → i < j → f i < f j) ∧
        (∀ i j : Nat, i < n → j < n → i ≠ j →
          E (f i) (f j) = A i j) := by
    induction n with
    | zero =>
        intro _
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro i j hi hj hij
          omega
        · intro i j hi hj hij
          omega
    | succ n ih =>
        intro hFreeSucc
        have hFreeOld : ¬ HasCliqueBelow A n ell := by
          rintro ⟨s,hsCard,hsBelow,hsClique⟩
          apply hFreeSucc
          exact ⟨s,hsCard,
            (by intro x hx; exact Nat.lt_succ_of_lt (hsBelow x hx)),
            hsClique⟩
        obtain ⟨f,hMono,hGraph⟩ := ih hFreeOld
        let P : Finset Nat := Finset.range n
        let S : Finset Nat := P.filter (fun x => A x n = true)
        have hSP : S ⊆ P := Finset.filter_subset _ _
        have hSafe : finitePoolCliqueCheck A (ell-1) S = false := by
          apply (finitePoolCliqueCheck_false_iff A (ell-1) S).2
          rintro ⟨s,hsS,hsCard,hsClique⟩
          have hNbr : HasNeighbourCliqueBelow A n (ell-1)
              (fun x => A x n) := by
            refine ⟨s,hsCard,?_,hsClique⟩
            intro x hx
            have h := Finset.mem_filter.mp (hsS hx)
            exact ⟨Finset.mem_range.mp h.1,h.2⟩
          exact hFreeSucc
            ((hasCliqueBelow_succ_iff_old_or_neighbour
              A n ell hell hASym hALoops).2 (Or.inr hNbr))
        let front : Nat := (P.sup f) + 1
        have hBelow : ∀ x ∈ P, f x < front := by
          intro x hx
          have hLe : f x ≤ P.sup f := Finset.le_sup (f := f) hx
          exact Nat.lt_succ_of_le hLe
        have hInj : Set.InjOn f ↑P := by
          intro x hx y hy heq
          have hxN : x < n := Finset.mem_range.mp hx
          have hyN : y < n := Finset.mem_range.mp hy
          rcases lt_trichotomy x y with hxy | hEq | hyx
          · have hLt := hMono x y hxN hyN hxy
            omega
          · exact hEq
          · have hLt := hMono y x hyN hxN hyx
            omega
        have hOldAtoms :
            ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
              A x y = E (f x) (f y) := by
          intro x hx y hy hxy
          exact (hGraph x y
            (Finset.mem_range.mp hx)
            (Finset.mem_range.mp hy) hxy).symm
        have hForward : ∀ x ∈ P,
            A x n = decide (x ∈ S) := by
          intro x hx
          by_cases hb : A x n = true
          · have hs : x ∈ S := Finset.mem_filter.mpr ⟨hx,hb⟩
            simp [hb,hs]
          · have hFalse : A x n = false := by
              cases hVal : A x n with
              | false => rfl
              | true => exact False.elim (hb hVal)
            have hs : x ∉ S := by
              intro hMem
              exact hb (Finset.mem_filter.mp hMem).2
            simp [hFalse,hs]
        have hBackward : ∀ x ∈ P,
            A n x = A x n := by
          intro x hx
          exact hASym n x
        obtain ⟨v,hFront,hColumn,hGaps⟩ :=
          onePointLeftDense_extend_finite_induced_copy
            A E ell front n hell hDense (hEFree front)
            P S hSP f hInj hBelow hOldAtoms
            hForward hBackward hSafe
        let f' : Nat → Nat := fun i => if i = n then v else f i
        refine ⟨f', ?_, ?_⟩
        · intro i j hi hj hij
          by_cases hjn : j = n
          · have hin : i < n := by omega
            have hine : i ≠ n := by omega
            change (if i = n then v else f i) <
              (if j = n then v else f j)
            rw [if_neg hine, if_pos hjn]
            exact lt_of_lt_of_le
              (hBelow i (Finset.mem_range.mpr hin)) hFront
          · have hin : i < n := by omega
            have hjnlt : j < n := by omega
            have hine : i ≠ n := by omega
            change (if i = n then v else f i) <
              (if j = n then v else f j)
            rw [if_neg hine, if_neg hjn]
            exact hMono i j hin hjnlt hij
        · intro i j hi hj hne
          by_cases hin : i = n
          · have hjn : j ≠ n := by omega
            have hjlt : j < n := by omega
            change E (if i = n then v else f i)
              (if j = n then v else f j) = A i j
            rw [if_pos hin, if_neg hjn, hin]
            exact (hColumn j (Finset.mem_range.mpr hjlt)).2
          · by_cases hjn : j = n
            · have hilt : i < n := by omega
              change E (if i = n then v else f i)
                (if j = n then v else f j) = A i j
              rw [if_neg hin, if_pos hjn, hjn]
              exact (hColumn i (Finset.mem_range.mpr hilt)).1
            · have hilt : i < n := by omega
              have hjlt : j < n := by omega
              change E (if i = n then v else f i)
                (if j = n then v else f j) = A i j
              rw [if_neg hin, if_neg hjn]
              exact hGraph i j hilt hjlt hne
  exact construct N hAFree

/-- Specialization to the actual normalized Henson forbidden-family
semantics. Prefix K_ell-freeness of E is derived, while the fixed
enumeration's OnePointLeftDense hypothesis remains explicit. -/
theorem henson_leftDense_embeds_finite_KFree_pattern
    (ell : Nat) (hell : 2 ≤ ell)
    (A E : Nat → Nat → Bool)
    (hASym : ∀ i j, A i j = A j i)
    (hALoops : ∀ i, A i i = false)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (N : Nat) (hAFree : ¬ HasCliqueBelow A N ell) :
    ∃ f : Nat → Nat,
      (∀ i j : Nat, i < N → j < N → i < j → f i < f j) ∧
      (∀ i j : Nat, i < N → j < N → i ≠ j →
        E (f i) (f j) = A i j) := by
  exact onePointLeftDense_embeds_finite_KFree_pattern
    A E ell N (by omega) hASym hALoops hDense
    (hensonForbiddenFamily_no_prefix_cliques ell hell E hAvoid)
    hAFree

#print axioms onePointLeftDense_embeds_finite_KFree_pattern
#print axioms henson_leftDense_embeds_finite_KFree_pattern

end Kk
