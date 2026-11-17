import Kk.PartialNumericCapacityBounds
import Kk.FullRealGenerationCapacity
import Kk.NumericHReservedPrefixCapacity
import Mathlib.Tactic

/-!
# Track A: physical non-top numerical-H generation-height clique bound

English-first proof and sixteen hostile checks:
  docs/partial_numeric_generation_height_english_audit.md

Any actual directed numerical-H ordinary-L clique in the even
partial old prefix containing a current-original b copy at
generation m<g<=k has cardinal at most m+1<=g.

The key proof has no selected-shadow shortcut: every other
clique member has a real generation STRICTLY below m and
these generation values are injective on the remaining clique.
This is the physical upper-height part of the sharp partial
capacity formula, not the remaining original-adjacency
capacity or lower staircase witness.
-/

namespace Kk

open SuccessorTree.V10

/-- A noncomputable total generation decoder. On a bounded
real numeric coordinate hPosition k i q (q<=k), it selects
the uniquely determined actual generation q. Values at odd
dummies or out-of-range inputs are irrelevant. -/
noncomputable def numericHRealGeneration (k z : Nat) : Nat := by
  classical
  exact if h : ∃ i : Nat, ∃ q : Nat,
      q ≤ k ∧ hPosition k i q = z then
    Classical.choose (Classical.choose_spec h)
  else 0

theorem numericHRealGeneration_at
    (k i q : Nat) (hq : q ≤ k) :
    numericHRealGeneration k (hPosition k i q) = q := by
  classical
  unfold numericHRealGeneration
  split_ifs with h
  · have hSpec := Classical.choose_spec h
    have hGen := Classical.choose_spec hSpec
    exact (hPosition_injective_bounded k
      (Classical.choose h)
      (Classical.choose hSpec) i q
      hGen.1 hq hGen.2).2
  · exact False.elim (h ⟨i,q,hq,rfl⟩)

/-- A TRUE positive numerical-H L edge between two bounded
real coordinates strictly below the top generation cannot
join equal generations. The proof checks BOTH source-name
orders and excludes the top-top exceptional gate. -/
theorem finiteNumericH_real_positive_below_top_generations_ne
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M i j q m : Nat)
    (hq : q < k) (hm : m < k)
    (hEdge :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k i q) (hPosition k j m)
        (0 : Fin 1) = true) : q ≠ m := by
  have hqLe : q ≤ k := by omega
  have hmLe : m ≤ k := by omega
  have hOrigNe :=
    (finiteNumericH_real_positive_projects_original
      E k M i j q m hqLe hmLe hEdge).1
  by_cases hij : i < j
  · have hGate :
        q < m ∨ (q = k ∧ m = k) := by
      have hRawGate := ((hNumericBinary_real_forward_iff
        (normalizedGraphModel E).binary k i j q m
        (0 : Fin 1) hij hqLe hmLe).mp hEdge).1
      omega
    omega
  · have hji : j < i := by omega
    have hReverse :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k j m) (hPosition k i q)
          (0 : Fin 1) = true :=
      (henson_finiteNumericH_binary_symmetric
        E hSym k M (hPosition k i q)
        (hPosition k j m)).symm.trans hEdge
    have hGate :
        m < q ∨ (m = k ∧ q = k) := by
      have hRawGate := ((hNumericBinary_real_forward_iff
        (normalizedGraphModel E).binary k j i m q
        (0 : Fin 1) hji hmLe hqLe).mp hReverse).1
      omega
    omega

/-- If an actual numerical-H clique in the EVEN old partial
prefix contains one real copy of the current original b at
non-top generation m<g<=k, its size is at most g.

All other old members have distinct generations strictly <m,
so erasing that current copy injects the clique into [0,m).
This works for arbitrary older original names, not just
consecutive members of a reserved clique block. -/
theorem finiteNumericH_partial_current_clique_card_le_cut
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b g M : Nat) (hg : g ≤ k)
    (s : Finset Nat)
    (hs : s ⊆ numericHPartialRealPool k b g)
    (hc : IsDirectedCliqueOn
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary
          x y (0 : Fin 1)) s)
    (m : Nat) (hm : m < g)
    (hv : hPosition k b m ∈ s) :
    s.card ≤ g := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1)
  let v : Nat := hPosition k b m
  have hmK : m < k := lt_of_lt_of_le hm hg
  have hmLe : m ≤ k := by omega
  have hMap : Set.MapsTo (numericHRealGeneration k)
      ↑(s.erase v) ↑(Finset.range m) := by
    intro x hx
    have hxErase : x ∈ s.erase v := Finset.mem_coe.mp hx
    obtain ⟨hxNe,hxS⟩ := Finset.mem_erase.mp hxErase
    obtain ⟨i,q,hi,hq,hEq,_⟩ :=
      numericH_partial_real_repr k b g x hg (hs hxS)
    have hEdge :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k b m)
          (0 : Fin 1) = true := by
      rw [←hEq]
      exact hc x hxS v hv hxNe
    have hOrigNe :=
      (finiteNumericH_real_positive_projects_original
        E k M i b q m hq hmLe hEdge).1
    have hiLt : i < b := by omega
    have hGate :
        q < m ∨ (q = k ∧ m = k) := by
      have hRawGate := ((hNumericBinary_real_forward_iff
        (normalizedGraphModel E).binary k i b q m
        (0 : Fin 1) hiLt hq hmLe).mp hEdge).1
      omega
    have hqLt : q < m := by omega
    have hDecode :
        numericHRealGeneration k x = q := by
      rw [hEq]
      exact numericHRealGeneration_at k i q hq
    apply Finset.mem_coe.mpr
    apply Finset.mem_range.mpr
    rw [hDecode]
    exact hqLt
  have hInj : Set.InjOn (numericHRealGeneration k)
      ↑(s.erase v) := by
    intro x hx y hy hGenEq
    by_contra hxy
    have hxS : x ∈ s :=
      (Finset.mem_erase.mp (Finset.mem_coe.mp hx)).2
    have hyS : y ∈ s :=
      (Finset.mem_erase.mp (Finset.mem_coe.mp hy)).2
    obtain ⟨i,q,hi,hq,hxEq,_⟩ :=
      numericH_partial_real_repr k b g x hg (hs hxS)
    obtain ⟨j,n,hj,hn,hyEq,_⟩ :=
      numericH_partial_real_repr k b g y hg (hs hyS)
    have hqLt : q < m := by
      have hBound := Finset.mem_range.mp
        (Finset.mem_coe.mp (hMap hx))
      rw [hxEq,numericHRealGeneration_at k i q hq] at hBound
      exact hBound
    have hnLt : n < m := by
      have hBound := Finset.mem_range.mp
        (Finset.mem_coe.mp (hMap hy))
      rw [hyEq,numericHRealGeneration_at k j n hn] at hBound
      exact hBound
    have hEdge :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i q) (hPosition k j n)
          (0 : Fin 1) = true := by
      rw [←hxEq,←hyEq]
      exact hc x hxS y hyS hxy
    have hGenNe :=
      finiteNumericH_real_positive_below_top_generations_ne
        E hSym k M i j q n
        (lt_trans hqLt hmK)
        (lt_trans hnLt hmK) hEdge
    have hQN : q = n := by
      rw [hxEq,hyEq,
        numericHRealGeneration_at k i q hq,
        numericHRealGeneration_at k j n hn] at hGenEq
      exact hGenEq
    exact hGenNe hQN
  have hCardBound : (s.erase v).card ≤ m := by
    have h :=
      Finset.card_le_card_of_injOn
        (s := s.erase v) (t := Finset.range m)
        (numericHRealGeneration k) hMap hInj
    simpa only [Finset.card_range] using h
  have hErase : (s.erase v).card + 1 = s.card :=
    Finset.card_erase_add_one hv
  omega

#print axioms Kk.numericHRealGeneration_at
#print axioms Kk.finiteNumericH_real_positive_below_top_generations_ne
#print axioms Kk.finiteNumericH_partial_current_clique_card_le_cut

end Kk
