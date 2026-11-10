import Kk.ReservedPrefixCapacity
import Kk.IsolatedBlockContinuationAge
import Kk.HensonZeroGenerationClique
import Kk.NumericHDesignatedPositive
import Mathlib.Tactic

/-!
# Physical single-block prefix capacities in the genuine numerical H

English argument and hostile audit were committed FIRST in
`docs/actual_numeric_h_reserved_prefix_bridge_english_audit.md`.
All copies are real positions of consecutive reserved ORIGINAL labels.
We use ordinary graph L.binary, NOT auxiliary Kpt E incidence.
This does not claim a simultaneous entire marked-front age or a global
inverse-source orbit.
-/

namespace Kk

open SuccessorTree.V10

/-- Physical position of a labelled copy in a consecutive reserved block. -/
def reservedBlockNumericPos (k N : Nat) (x : Nat × Nat) : Nat :=
  hPosition k (N + x.1) x.2

/-- The genuine finite set of real numbered H coordinates below the
    designated reserved original/generation pivot. -/
def reservedBlockNumericPrefix (k N a g : Nat) : Finset Nat :=
  (reservedPrefixPool k a g).image (reservedBlockNumericPos k N)

private theorem reservedPrefixPool_bounds (k a g : Nat)
    (x : Nat × Nat) (hx : x ∈ reservedPrefixPool k a g) :
    x.1 ≤ a ∧ x.2 ≤ k ∧ (x.1 = a → x.2 ≤ g) := by
  have hh := Finset.mem_filter.mp hx
  have hprod := Finset.mem_product.mp hh.1
  have hb := Finset.mem_range.mp hprod.1
  have ht := Finset.mem_range.mp hprod.2
  rcases hh.2 with hla | ⟨hla,hlg⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩

/-- The ACTUAL numerical H position map is injective on the bounded
    real-copy prefix, including distinct generations of the same original. -/
theorem reservedBlockNumericPos_injOn (k N a g : Nat) :
    Set.InjOn (reservedBlockNumericPos k N)
      ↑(reservedPrefixPool k a g) := by
  intro x hx y hy heq
  have hxGen := (reservedPrefixPool_bounds k a g x hx).2.1
  have hyGen := (reservedPrefixPool_bounds k a g y hy).2.1
  have hMatch := hPosition_injective_bounded k
    (N + x.1) x.2 (N + y.1) y.2 hxGen hyGen heq
  apply Prod.ext
  · omega
  · exact hMatch.2

/-- The actual H generator requires STRICTLY distinct original indices.
    It cannot create a binary edge joining two real copies of one original,
    regardless of their bounded generations or the base graph's loops. -/
theorem hNumericBinary_same_original_false
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i q m : Nat) (t : Fin d)
    (hq : q ≤ k) (hm : m ≤ k) :
    hNumericBinary B k (hPosition k i q) (hPosition k i m) t = false := by
  by_cases hbit :
      hNumericBinary B k (hPosition k i q) (hPosition k i m) t = true
  · obtain ⟨u,v,s,n,huv,hs,hn,_,hdir⟩ :=
      (hNumericBinary_true_iff B k _ _ t).mp hbit
    rcases hdir with ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩
    · have hi := (hPosition_injective_bounded k i q u s hq hs hx).1
      have hj := (hPosition_injective_bounded k i m v n hm hn hy).1
      omega
    · have hi := (hPosition_injective_bounded k i q v n hq hn hx).1
      have hj := (hPosition_injective_bounded k i m u s hm hs hy).1
      omega
  · cases h : hNumericBinary B k (hPosition k i q)
        (hPosition k i m) t with
    | false => rfl
    | true => exact False.elim (hbit h)

/-- Both orientations of every binary graph atom on the real reserved
    copies agree with the precise generation gate. -/
theorem finiteNumericH_reserved_block_exact_gate
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g : Nat)
    (ha : a < r)
    (hClique : ∀ b c, b < c → c < r → E (N+b) (N+c) = true)
    (x y : Nat × Nat)
    (hx : x ∈ reservedPrefixPool k a g)
    (hy : y ∈ reservedPrefixPool k a g)
    (hxy : x ≠ y) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (reservedBlockNumericPos k N x)
        (reservedBlockNumericPos k N y) (0 : Fin 1) = true ↔
      reservedCopyEdge k x y := by
  have hxGen := (reservedPrefixPool_bounds k a g x hx).2.1
  have hyGen := (reservedPrefixPool_bounds k a g y hy).2.1
  have hxLabel := (reservedPrefixPool_bounds k a g x hx).1
  have hyLabel := (reservedPrefixPool_bounds k a g y hy).1
  change hNumericBinary (normalizedGraphModel E).binary k
    (hPosition k (N+x.1) x.2)
    (hPosition k (N+y.1) y.2) (0 : Fin 1) = true ↔
      reservedCopyEdge k x y
  by_cases hForward : x.1 < y.1
  · have hOriginal :
        (normalizedGraphModel E).binary
          (N+x.1) (N+y.1) (0 : Fin 1) = true := by
      change E (N+x.1) (N+y.1) = true
      exact hClique x.1 y.1 hForward (by omega)
    have hOrigLt : N+x.1 < N+y.1 := by omega
    rw [hNumericBinary_real_forward_iff
      (normalizedGraphModel E).binary k
      (N+x.1) (N+y.1) x.2 y.2 (0 : Fin 1)
      hOrigLt hxGen hyGen]
    simp [reservedCopyEdge, hForward, hOriginal]
  · by_cases hReverse : y.1 < x.1
    · have hOriginal :
          (normalizedGraphModel E).binary
            (N+y.1) (N+x.1) (0 : Fin 1) = true := by
        change E (N+y.1) (N+x.1) = true
        exact hClique y.1 x.1 hReverse (by omega)
      have hOrigLt : N+y.1 < N+x.1 := by omega
      have hBSym : ∀ i j t,
          (normalizedGraphModel E).binary i j t =
            (normalizedGraphModel E).binary j i t := by
        intro i j t
        fin_cases t
        change E i j = E j i
        exact hSym i j
      rw [hNumericBinary_symmetric_of_base
        (normalizedGraphModel E).binary hBSym k
        (hPosition k (N+x.1) x.2)
        (hPosition k (N+y.1) y.2) (0 : Fin 1)]
      rw [hNumericBinary_real_forward_iff
        (normalizedGraphModel E).binary k
        (N+y.1) (N+x.1) y.2 x.2 (0 : Fin 1)
        hOrigLt hyGen hxGen]
      simp [reservedCopyEdge, hForward, hReverse, hOriginal]
    · have hSame : x.1 = y.1 := by omega
      have hZero : hNumericBinary (normalizedGraphModel E).binary k
        (hPosition k (N+x.1) x.2)
        (hPosition k (N+y.1) y.2) (0 : Fin 1) = false := by
        rw [← hSame]
        exact hNumericBinary_same_original_false
          (normalizedGraphModel E).binary k (N+x.1) x.2 y.2
          (0 : Fin 1) hxGen hyGen
      rw [hZero]
      simp [reservedCopyEdge, hSame]

/-- Both finite-capacity definitions search the exact SAME directed
    clique subsets. This equality is extensional, not a new age axiom. -/
theorem reservedImageCliqueCapacity_eq_finiteDirectedCliqueCapacity
    (E : Nat → Nat → Bool) (Q : Finset Nat) :
    reservedImageCliqueCapacity E Q = finiteDirectedCliqueCapacity E Q := by
  classical
  have hFilter : Q.powerset.filter (IsNumericBoolClique E) =
      Q.powerset.filter (fun s =>
        ∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true) := by
    ext s
    simp only [Finset.mem_filter, IsNumericBoolClique]
  unfold reservedImageCliqueCapacity finiteDirectedCliqueCapacity
  exact congrArg (fun p : Finset (Finset Nat) => p.sup Finset.card) hFilter

/-- Sharp single-block capacity in the literal FINITE numerical-H L
    relation. It does not yet assume the copied points are in the carrier. -/
theorem finiteNumericH_reserved_block_prefix_capacity
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g : Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hClique : ∀ b c, b < c → c < r → E (N+b) (N+c) = true) :
    finiteDirectedCliqueCapacity
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      (reservedBlockNumericPrefix k N a g) =
      if g < a then a else a+1 := by
  rw [← reservedImageCliqueCapacity_eq_finiteDirectedCliqueCapacity]
  exact reservedImageCliqueCapacity_eq_of_gate
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    (reservedBlockNumericPos k N) k r a g ha hr hgk
    (reservedBlockNumericPos_injOn k N a g)
    (fun x hx y hy hxy =>
      finiteNumericH_reserved_block_exact_gate E hSym
        k N M r a g ha hClique x y hx hy hxy)

#print axioms reservedBlockNumericPos_injOn
#print axioms hNumericBinary_same_original_false
#print axioms finiteNumericH_reserved_block_exact_gate
#print axioms reservedImageCliqueCapacity_eq_finiteDirectedCliqueCapacity
#print axioms finiteNumericH_reserved_block_prefix_capacity

end Kk
