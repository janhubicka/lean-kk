import Kk.PartialNumericGenerationHeight
import Kk.FullRealGenerationCapacity
import Kk.NumericHReservedPrefixCapacity
import Mathlib.Tactic

/-!
# Track A: original-neighbour clique capacity of an actual partial current-b clique

Proof and adversarial audit were committed FIRST:
  docs/partial_numeric_current_link_upper_english_audit.md

Any actual numerical-H clique using a non-top current original b
copy in a partial block contains no other copy of b. Erasing this
copy leaves a clique of complete earlier real copies whose original
index image is injective, a genuine E clique, and entirely linked
to b. Therefore card(s)<=1+cap_E({i in P:E(i,b)=true}).

This is the ORIGINAL-link half of the upper bound of the sharp
partial-cut formula. The generation-height bound and lower staircase
witness are separate. No full Kpt E/B3 or Ramsey theorem is claimed.
-/

namespace Kk

open SuccessorTree.V10

/-- An actual numerical-H L clique in all real generations of P
plus the current original's partial generation range, containing
one current-b copy, has cardinal at most one plus the maximum
ORIGINAL E clique among names from P positively adjacent to b.

No assumption that P is a clique or consists of consecutive
original names; same-original H edges are literally impossible.
This theorem needs no original E symmetry. -/
theorem finiteNumericH_partial_current_clique_card_le_link_cap
    (E : Nat → Nat → Bool)
    (k b g M : Nat) (hg : g ≤ k)
    (P s : Finset Nat)
    (hs : s ⊆ numericHCompleteRealPool k P ∪
      (Finset.range g).image (fun q => hPosition k b q))
    (hc : IsDirectedCliqueOn
      (fun x y => (finiteNumericHL
        (normalizedGraphModel E) k M).binary x y (0 : Fin 1)) s)
    (m : Nat) (hm : m < g)
    (hv : hPosition k b m ∈ s) :
    s.card ≤ 1 + finiteDirectedCliqueCapacity E
      (P.filter (fun i => E i b = true)) := by
  classical
  let L : Nat → Nat → Bool :=
    fun x y => (finiteNumericHL
      (normalizedGraphModel E) k M).binary x y (0 : Fin 1)
  let v : Nat := hPosition k b m
  have hmLe : m ≤ k := by omega
  have hRestSub :
      s.erase v ⊆ numericHCompleteRealPool k P := by
    intro z hz
    obtain ⟨hzNe,hzS⟩ := Finset.mem_erase.mp hz
    rcases Finset.mem_union.mp (hs hzS) with hEarlier | hCurrent
    · exact hEarlier
    · obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hCurrent
      have hqLe : q ≤ k := by
        have hqLt : q < g := Finset.mem_range.mp hq
        omega
      have hEdge :
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k b q) (hPosition k b m)
            (0 : Fin 1) = true := by
        rw [hEq]
        exact hc z hzS v hv hzNe
      have hZero :
          (finiteNumericHL (normalizedGraphModel E) k M).binary
            (hPosition k b q) (hPosition k b m)
            (0 : Fin 1) = false := by
        change hNumericBinary (normalizedGraphModel E).binary k
          (hPosition k b q) (hPosition k b m)
          (0 : Fin 1) = false
        exact hNumericBinary_same_original_false
          (normalizedGraphModel E).binary k b q m
          (0 : Fin 1) hqLe hmLe
      rw [hZero] at hEdge
      contradiction
  have hRestClique : IsDirectedCliqueOn L (s.erase v) := by
    intro x hx y hy hxy
    exact hc x (Finset.mem_erase.mp hx).2
      y (Finset.mem_erase.mp hy).2 hxy
  have hInj := finiteNumericH_real_clique_original_inj
    E k M P (s.erase v) hRestSub hRestClique
  have hImageClique := finiteNumericH_real_clique_original_image
    E k M P (s.erase v) hRestSub hRestClique
  have hImageSub :
      (s.erase v).image (numericHRealOriginal k) ⊆
        P.filter (fun i => E i b = true) := by
    intro i hi
    obtain ⟨z,hz,hIz⟩ := Finset.mem_image.mp hi
    obtain ⟨i',hi',q,hq,hZ⟩ :=
      (numericHCompleteRealPool_mem_iff k P z).mp
        (hRestSub hz)
    have hDecode : numericHRealOriginal k z = i' := by
      rw [←hZ]
      exact numericHRealOriginal_at k i' q hq
    have hzS : z ∈ s := (Finset.mem_erase.mp hz).2
    have hzNe : z ≠ v := (Finset.mem_erase.mp hz).1
    have hEdge :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k i' q) (hPosition k b m)
          (0 : Fin 1) = true := by
      rw [hZ]
      exact hc z hzS v hv hzNe
    have hE :=
      (finiteNumericH_real_positive_projects_original
        E k M i' b q m hq hmLe hEdge).2
    have hiEq : i = i' := hIz.symm.trans hDecode
    rw [hiEq]
    exact Finset.mem_filter.mpr ⟨hi',hE⟩
  have hCapBound := directedClique_card_le_capacity
    E (P.filter (fun i => E i b = true))
      ((s.erase v).image (numericHRealOriginal k))
      hImageSub hImageClique
  have hCardImage := Finset.card_image_iff.mpr hInj
  rw [hCardImage] at hCapBound
  have hErase : (s.erase v).card + 1 = s.card :=
    Finset.card_erase_add_one hv
  omega

#print axioms Kk.finiteNumericH_partial_current_clique_card_le_link_cap

end Kk
