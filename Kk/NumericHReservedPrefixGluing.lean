import Kk.NumericHReservedPrefixCapacity
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Genuine finite numerical-H reserved prefix carrier and gluing

The English proof and adversarial audit were committed BEFORE this file in
\`docs/physical_reserved_prefix_carrier_gluing_english_audit.md\`.

These are literal H binary L atoms and actual finite numerical coordinates.
The gluing interface demands explicit old/reserve, gap/future, and both-direction
reserve/future support columns, as well as the entire past clique check.
It does NOT presume or prove those hypotheses for the unbounded resolved diary.
The auxiliary E relation is not used for graph clique capacity.
-/

namespace Kk

open SuccessorTree.V10

/-- Every real reserved-copy prefix coordinate is strictly before the
numerical H carrier cut if the pivot coordinate is before that cut.
Crucially, an earlier original's TOP copy still lies before the pivot
even if its generation is larger than the pivot generation. -/
theorem reservedBlockNumericPrefix_inside_carrier
    (k N M a g : Nat)
    (hCut : hPosition k (N+a) g < M) :
    ∀ u ∈ reservedBlockNumericPrefix k N a g, u < M := by
  intro u hu
  obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp hu
  have hFilter := Finset.mem_filter.mp hx
  have hProduct := Finset.mem_product.mp hFilter.1
  have hBlock : x.1 ≤ a := by
    have h := Finset.mem_range.mp hProduct.1
    omega
  have hGen : x.2 ≤ k := by
    have h := Finset.mem_range.mp hProduct.2
    omega
  have hPivotGen : x.1 = a → x.2 ≤ g := by
    intro hEq
    rcases hFilter.2 with hLt | ⟨_,hBound⟩
    · omega
    · exact hBound
  have hLe :
      reservedBlockNumericPos k N x ≤ hPosition k (N+a) g := by
    by_cases hPivot : x.1 = a
    · have hg := hPivotGen hPivot
      change hPosition k (N+x.1) x.2 ≤ hPosition k (N+a) g
      rw [hPivot]
      unfold hPosition
      omega
    · have hBefore : x.1 < a := by omega
      change hPosition k (N+x.1) x.2 ≤ hPosition k (N+a) g
      exact Nat.le_of_lt
        (hPosition_lt_of_block_lt k (N+x.1) (N+a)
          x.2 g hGen (by omega))
  rw [← heq]
  omega

/-- The prefix is a genuine subset of the actual finite H L carrier,
not merely an abstract set of real H coordinates. -/
theorem reservedBlockNumericPrefix_mem_finiteH
    (E : Nat → Nat → Bool) (k N M a g : Nat)
    (hCut : hPosition k (N+a) g < M) :
    ∀ u ∈ reservedBlockNumericPrefix k N a g,
      u ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  intro u hu
  change u < M
  exact reservedBlockNumericPrefix_inside_carrier k N M a g hCut u hu

/-- Exact entire finite continuation criterion after inserting a REAL
reserved numerical-H block prefix. Neither the reserved prefix Q nor
the supported future U is assumed to be a clique.

The old/gap/future L-column hypotheses and the entire past test are
EXPLICIT. The imported physical H capacity formula is substituted into
the already proved nontrivial complete-join gluing equivalence. -/
theorem finiteNumericH_reserved_prefix_gluing_iff
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g ell : Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hClique : ∀ b c, b < c → c < r → E (N+b) (N+c) = true)
    (P G W U : Finset Nat)
    (hQU : Disjoint (reservedBlockNumericPrefix k N a g) U)
    (hU : U ⊆ W)
    (hNoPQ :
      ∀ p ∈ P, ∀ q ∈ reservedBlockNumericPrefix k N a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p q (0 : Fin 1) = false)
    (hNoGW :
      ∀ z ∈ G, ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z w (0 : Fin 1) = false)
    (hSupport :
      ∀ q ∈ reservedBlockNumericPrefix k N a g, ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          q w (0 : Fin 1) = decide (w ∈ U) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w q (0 : Fin 1) = decide (w ∈ U))
    (hPast :
      finitePoolCliqueCheck
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        ell ((P ∪ reservedBlockNumericPrefix k N a g) ∪ G) = false) :
    finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (((P ∪ reservedBlockNumericPrefix k N a g) ∪ G) ∪ W) = false ↔
      finitePoolCliqueCheck
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        ell (P ∪ W) = false ∧
      (if g < a then a else a+1) +
        finiteDirectedCliqueCapacity
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1)) U < ell := by
  have hExact := finitePoolCliqueCheck_isolated_block_gluing_iff
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    ell P (reservedBlockNumericPrefix k N a g) G W U
    hQU hU hNoPQ hNoGW hSupport hPast
  rw [finiteNumericH_reserved_block_prefix_capacity
    E hSym k N M r a g ha hr hgk hClique] at hExact
  exact hExact

#print axioms reservedBlockNumericPrefix_inside_carrier
#print axioms reservedBlockNumericPrefix_mem_finiteH
#print axioms finiteNumericH_reserved_prefix_gluing_iff

end Kk
