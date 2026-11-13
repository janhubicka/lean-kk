import Kk.RelativeMarkedFrontAge
import Kk.NumericHReservedPrefixCapacity
import Mathlib.Tactic

/-!
# Track A: physical reserved-prefix capacities for nonconsecutive originals

English proof and hostile audit first:
  docs/nonconsecutive_reserved_prefix_english_audit.md

The selected reserved original indices need only be STRICTLY ORDERED,
not consecutive. Every edge is evaluated in the unchanged original E
at the actual q(b) indices, with the exact numerical-H generation gate.

This proves ordinary graph L capacities and an explicitly conditional
all-marked-front gluing test. It neither creates the original schedule
nor disposes of gaps or auxiliary Kpt E/parameter-closed B3.
-/

namespace Kk

open SuccessorTree.V10

/-- Literal H coordinate for a real generation of the b-th (not
necessarily consecutively indexed) reserved original. -/
def orderedReservedNumericPos (k : Nat) (q : Nat → Nat)
    (x : Nat × Nat) : Nat :=
  hPosition k (q x.1) x.2

/-- Real H-coordinate prefix through the generation-g copy of the
a-th original in an ordered, possibly nonconsecutive reserved block. -/
def orderedReservedNumericPrefix (k : Nat) (q : Nat → Nat)
    (a g : Nat) : Finset Nat :=
  (reservedPrefixPool k a g).image (orderedReservedNumericPos k q)

private theorem orderedReservedPrefix_pair_bounds
    (k a g : Nat) (x : Nat × Nat)
    (hx : x ∈ reservedPrefixPool k a g) :
    x.1 ≤ a ∧ x.2 ≤ k ∧ (x.1 = a → x.2 ≤ g) := by
  have hFiltered := Finset.mem_filter.mp hx
  have hProd := Finset.mem_product.mp hFiltered.1
  have hb := Finset.mem_range.mp hProd.1
  have ht := Finset.mem_range.mp hProd.2
  rcases hFiltered.2 with hlt | ⟨heq,hg⟩
  · exact ⟨by omega,by omega,by omega⟩
  · exact ⟨by omega,by omega,by omega⟩

/-- No collisions of real coordinates, even when selected original
labels have arbitrary gaps. Strict order is only required below r. -/
theorem orderedReservedNumericPos_injOn
    (k r a g : Nat) (q : Nat → Nat)
    (ha : a < r)
    (hOrder : ∀ b c, b < c → c < r → q b < q c) :
    Set.InjOn (orderedReservedNumericPos k q)
      ↑(reservedPrefixPool k a g) := by
  intro x hx y hy heq
  have hxBounds := orderedReservedPrefix_pair_bounds k a g x hx
  have hyBounds := orderedReservedPrefix_pair_bounds k a g y hy
  have hMatch := hPosition_injective_bounded k
    (q x.1) x.2 (q y.1) y.2
    hxBounds.2.1 hyBounds.2.1 heq
  have hxWithin : x.1 < r := by omega
  have hyWithin : y.1 < r := by omega
  have hLabel : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hxy | hxy | hyx
    · have hStrict := hOrder x.1 y.1 hxy hyWithin
      omega
    · exact hxy
    · have hStrict := hOrder y.1 x.1 hyx hxWithin
      omega
  exact Prod.ext hLabel hMatch.2

/-- Every distinct ordered pair of real copies has the EXACT graph
L bit given by the reserved generation gate, including absent bits. -/
theorem finiteNumericH_ordered_reserved_exact_gate
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g : Nat) (q : Nat → Nat)
    (ha : a < r)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (x y : Nat × Nat)
    (hx : x ∈ reservedPrefixPool k a g)
    (hy : y ∈ reservedPrefixPool k a g)
    (hxy : x ≠ y) :
    (finiteNumericHL (normalizedGraphModel E) k M).binary
        (orderedReservedNumericPos k q x)
        (orderedReservedNumericPos k q y) (0 : Fin 1) = true ↔
      reservedCopyEdge k x y := by
  have hxBounds := orderedReservedPrefix_pair_bounds k a g x hx
  have hyBounds := orderedReservedPrefix_pair_bounds k a g y hy
  have hxWithin : x.1 < r := by omega
  have hyWithin : y.1 < r := by omega
  change hNumericBinary (normalizedGraphModel E).binary k
    (hPosition k (q x.1) x.2)
    (hPosition k (q y.1) y.2) (0 : Fin 1) = true ↔
      reservedCopyEdge k x y
  by_cases hForward : x.1 < y.1
  · have hOriginal :
        (normalizedGraphModel E).binary
          (q x.1) (q y.1) (0 : Fin 1) = true := by
      change E (q x.1) (q y.1) = true
      exact hClique x.1 y.1 hForward hyWithin
    have hOrigLt : q x.1 < q y.1 :=
      hOrder x.1 y.1 hForward hyWithin
    rw [hNumericBinary_real_forward_iff
      (normalizedGraphModel E).binary k
      (q x.1) (q y.1) x.2 y.2 (0 : Fin 1)
      hOrigLt hxBounds.2.1 hyBounds.2.1]
    simp [reservedCopyEdge, hForward, hOriginal] <;> omega
  · by_cases hReverse : y.1 < x.1
    · have hOriginal :
          (normalizedGraphModel E).binary
            (q y.1) (q x.1) (0 : Fin 1) = true := by
        change E (q y.1) (q x.1) = true
        exact hClique y.1 x.1 hReverse hxWithin
      have hOrigLt : q y.1 < q x.1 :=
        hOrder y.1 x.1 hReverse hxWithin
      have hBSym : ∀ i j t,
          (normalizedGraphModel E).binary i j t =
            (normalizedGraphModel E).binary j i t := by
        intro i j t
        fin_cases t
        change E i j = E j i
        exact hSym i j
      rw [hNumericBinary_symmetric_of_base
        (normalizedGraphModel E).binary hBSym k
        (hPosition k (q x.1) x.2)
        (hPosition k (q y.1) y.2) (0 : Fin 1)]
      rw [hNumericBinary_real_forward_iff
        (normalizedGraphModel E).binary k
        (q y.1) (q x.1) y.2 x.2 (0 : Fin 1)
        hOrigLt hyBounds.2.1 hxBounds.2.1]
      simp [reservedCopyEdge, hForward, hReverse, hOriginal] <;> omega
    · have hSame : x.1 = y.1 := by omega
      have hZero :
        hNumericBinary (normalizedGraphModel E).binary k
          (hPosition k (q x.1) x.2)
          (hPosition k (q y.1) y.2) (0 : Fin 1) = false := by
        rw [← hSame]
        exact hNumericBinary_same_original_false
          (normalizedGraphModel E).binary k
          (q x.1) x.2 y.2 (0 : Fin 1)
          hxBounds.2.1 hyBounds.2.1
      rw [hZero]
      simp [reservedCopyEdge, hSame]

/-- Sharp clique capacity in the ACTUAL numerical H ordinary-L graph:
no consecutiveness of the original q labels is assumed. -/
theorem finiteNumericH_ordered_reserved_prefix_capacity
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true) :
    finiteDirectedCliqueCapacity
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      (orderedReservedNumericPrefix k q a g) =
      if g < a then a else a+1 := by
  rw [← reservedImageCliqueCapacity_eq_finiteDirectedCliqueCapacity]
  exact reservedImageCliqueCapacity_eq_of_gate
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    (orderedReservedNumericPos k q) k r a g ha hr hgk
    (orderedReservedNumericPos_injOn k r a g q ha hOrder)
    (fun x hx y hy hxy =>
      finiteNumericH_ordered_reserved_exact_gate
        E hSym k M r a g q ha hOrder hClique x y hx hy hxy)

/-- Every coordinate in the nonconsecutive reserved prefix is inside
the literal finite H carrier if the pivot coordinate is inside it.
The intervening originals are NOT silently omitted from the ambient
prefix; their separate zero-column obligations belong to G. -/
theorem orderedReservedNumericPrefix_inside_carrier
    (k r a g M : Nat) (q : Nat → Nat)
    (ha : a < r)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hCut : hPosition k (q a) g < M) :
    ∀ u ∈ orderedReservedNumericPrefix k q a g, u < M := by
  intro u hu
  obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp hu
  have hxBounds := orderedReservedPrefix_pair_bounds k a g x hx
  have hLe :
      orderedReservedNumericPos k q x ≤ hPosition k (q a) g := by
    by_cases hPivot : x.1 = a
    · change hPosition k (q x.1) x.2 ≤ hPosition k (q a) g
      rw [hPivot]
      unfold hPosition
      have hxG := hxBounds.2.2 hPivot
      omega
    · have hBefore : x.1 < a := by omega
      change hPosition k (q x.1) x.2 ≤ hPosition k (q a) g
      exact Nat.le_of_lt
        (hPosition_lt_of_block_lt k (q x.1) (q a) x.2 g
          hxBounds.2.1 (hOrder x.1 a hBefore ha))
  rw [← heq]
  omega

theorem orderedReservedNumericPrefix_mem_finiteH
    (E : Nat → Nat → Bool) (k r a g M : Nat)
    (q : Nat → Nat)
    (ha : a < r)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hCut : hPosition k (q a) g < M) :
    ∀ u ∈ orderedReservedNumericPrefix k q a g,
      u ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  intro u hu
  change u < M
  exact orderedReservedNumericPrefix_inside_carrier
    k r a g M q ha hOrder hCut u hu

/-- Fully labelled marked-front conditional age at an ACTUAL ordered
block. The reserved originals need not be consecutive, and every W
vertex (including those outside the selected support) is prescribed.
All physical old/gap/age-comparison premises remain explicit. -/
theorem finiteNumericH_ordered_marked_front_prefix_age_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g ell d : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool)
    (P G W : Finset Nat)
    (hDisjoint : Disjoint (orderedReservedNumericPrefix k q a g) W)
    (hNoPQ : ∀ p ∈ P, ∀ u ∈ orderedReservedNumericPrefix k q a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p u (0 : Fin 1) = false)
    (hNoGW : ∀ z ∈ G, ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z w (0 : Fin 1) = false)
    (hSupport : ∀ u ∈ orderedReservedNumericPrefix k q a g,
      ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          u w (0 : Fin 1) = decide (tau w ∈ T) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w u (0 : Fin 1) = decide (tau w ∈ T))
    (hPast : finitePoolCliqueCheck
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        ell ((P ∪ orderedReservedNumericPrefix k q a g) ∪ G) = false)
    (hOld : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p p' (0 : Fin 1) = A p p')
    (hFuture : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w w' (0 : Fin 1) = A w w')
    (hPhysicalColumns : ∀ p ∈ P, ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p w (0 : Fin 1) = c p (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w p (0 : Fin 1) = c p (tau w))
    (hReferenceColumns : ∀ p ∈ P, ∀ w ∈ W,
        A p w = c p (tau w) ∧ A w p = c p (tau w)) :
    finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (((P ∪ orderedReservedNumericPrefix k q a g) ∪ G) ∪ W) = false ↔
    finitePoolCliqueCheck A ell (P ∪ W) = false ∧
      (if g < a then a else a+1) +
        finiteDirectedCliqueCapacity
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1))
          (markedSupportPool d W tau T) < ell := by
  have hResult := finite_marked_front_gluing_iff_reference
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    A ell d tau T c P (orderedReservedNumericPrefix k q a g) G W
    hDisjoint hNoPQ hNoGW hSupport hPast hOld hFuture
    hPhysicalColumns hReferenceColumns
  rw [finiteNumericH_ordered_reserved_prefix_capacity
    E hSym k M r a g q ha hr hgk hOrder hClique] at hResult
  exact hResult

#print axioms Kk.orderedReservedNumericPos_injOn
#print axioms Kk.finiteNumericH_ordered_reserved_exact_gate
#print axioms Kk.finiteNumericH_ordered_reserved_prefix_capacity
#print axioms Kk.orderedReservedNumericPrefix_inside_carrier
#print axioms Kk.orderedReservedNumericPrefix_mem_finiteH
#print axioms Kk.finiteNumericH_ordered_marked_front_prefix_age_iff

end Kk
