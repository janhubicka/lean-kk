import Kk.FullNumericBlockPrefixAge
import Kk.NumericHFullSelectedColumn
import Mathlib.Tactic

/-!
# Track A: the ACTUAL full numbered numerical-H old column

English proof and fourteen hostile checks committed before Lean:
  docs/full_block_actual_top_column_english_audit.md

For every completed original-block prefix and every finite
family of strictly later top-original names, the TRUE numeric H
binary L crossing to each future top is the full pulled-back old
original column, in BOTH ordered orientations, at EVERY old
numeric coordinate (all bounded real generations and odd dummies).

This eliminates a finite adapter assumption from the full-prefix
age comparison; it does not realize a recursively prescribed
sequence of future names, certify mixed stagewise clique
neighbourhoods, or settle auxiliary Kpt E/B3 and labelled orbits.
-/

namespace Kk

open SuccessorTree.V10

/-- At every literal old numbered coordinate, the actual finite
numerical-H binary-L relation to any chosen later top original
equals the complete real-copy/odd-dummy old column, in BOTH
ordered directions. The future original names j(t) are given,
not produced by the resolved-copy recursion. -/
theorem finiteNumericH_full_block_actual_top_column_both
    {d : Nat} (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k b M : Nat) (j : Fin d → Nat)
    (hj : ∀ t, b ≤ j t)
    (z : Nat) (hz : z < hPosition k b 0)
    (t : Fin d) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        z (hPosition k (j t) k) (0 : Fin 1) =
      numericHFullBlockOldColumn k b
        (fun i u => E i (j u)) z t ∧
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k (j t) k) z (0 : Fin 1) =
      numericHFullBlockOldColumn k b
        (fun i u => E i (j u)) z t := by
  classical
  have hzRange :
      z ∈ Finset.range (hPosition k b 0) :=
    Finset.mem_range.mpr hz
  have hzParts :
      z ∈ numericHCompleteRealPool k (Finset.range b) ∪
        numericHFullBlockOddPool k b := by
    rw [←numericH_full_block_prefix_exact k b]
    exact hzRange
  rcases Finset.mem_union.mp hzParts with hReal | hOdd
  · obtain ⟨i,hi,q,hq,hEq⟩ :=
      (numericHCompleteRealPool_mem_iff k
        (Finset.range b) z).mp hReal
    have hib : i < b := Finset.mem_range.mp hi
    have hij : i < j t := lt_of_lt_of_le hib (hj t)
    have hForward :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) = E i (j t) := by
      rw [←hEq]
      change hNumericBinary (normalizedGraphModel E).binary k
        (hPosition k i q) (hPosition k (j t) k)
        (0 : Fin 1) = E i (j t)
      exact numericH_older_generation_to_top_exact
        (normalizedGraphModel E).binary k i (j t) q
        (0 : Fin 1) hij hq
    have hSwap :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) =
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (j t) k) z (0 : Fin 1) :=
      henson_finiteNumericH_binary_symmetric E hSym k M
        z (hPosition k (j t) k)
    have hCol :
        numericHFullBlockOldColumn k b
          (fun i u => E i (j u)) z t = E i (j t) := by
      rw [←hEq]
      exact numericH_full_block_real_column k b i q hib hq
        (fun i u => E i (j u)) t
    exact ⟨hForward.trans hCol.symm,
      (hSwap.symm.trans hForward).trans hCol.symm⟩
  · have hzParity : z % 2 = 1 :=
      (Finset.mem_filter.mp hOdd).2
    have hzForm : z = 2 * (z / 2) + 1 := by
      have hDiv := Nat.mod_add_div z 2
      omega
    have hZeroForward :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z (hPosition k (j t) k) (0 : Fin 1) = false := by
      rw [hzForm]
      exact (finiteNumericH_odd_dummy_to_top_zero
        E k M (z/2) (j t)).1
    have hZeroReverse :
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          (hPosition k (j t) k) z (0 : Fin 1) = false := by
      rw [hzForm]
      exact (finiteNumericH_odd_dummy_to_top_zero
        E k M (z/2) (j t)).2
    have hCol :
        numericHFullBlockOldColumn k b
          (fun i u => E i (j u)) z t = false :=
      numericH_full_block_odd_column k b z hOdd
        (fun i u => E i (j u)) t
    exact ⟨hZeroForward.trans hCol.symm,
      hZeroReverse.trans hCol.symm⟩

#print axioms Kk.finiteNumericH_full_block_actual_top_column_both

end Kk
