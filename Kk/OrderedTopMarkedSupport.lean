import Kk.NonconsecutiveReservedPrefix
import Kk.NumericHTopSupportPool
import Mathlib.Tactic

/-!
# KK Track A: exact all-front ordered reserved-to-selected-top columns

English proof and hostile audit committed FIRST:
  docs/ordered_top_marked_support_english_audit.md

Actual reserved original indices q(b) need only be ordered, not
consecutive. When EVERY selected original j is later and the entire
uniform original column E(q(b),j) has the exact support bit for its
numerical top sort, ALL reserved real-copy to selected top-copy L
atoms have that exact bit in BOTH directions. Out-of-support zeros
are as important as supported positive bits.

This is graph L only, not the auxiliary numerical-H+ Kpt E field.
Existence of the full chronological schedule, gap zeros, integer-age
reference semantics and common labelled orbit remain independent.
-/

namespace Kk

open SuccessorTree.V10

/-- A genuinely later selected top original coordinate cannot collide
with a real copy of any earlier ordered reserved original, including
when the indices between reserved originals are not selected. -/
theorem orderedReservedNumericPrefix_disjoint_topPool
    (k r a g : Nat) (q : Nat → Nat)
    (S : Finset Nat)
    (ha : a < r)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j) :
    Disjoint (orderedReservedNumericPrefix k q a g)
      (numericHTopPool k S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u huQ huS
  obtain ⟨x,hx,hxEq⟩ := Finset.mem_image.mp huQ
  obtain ⟨j,hj,hjEq⟩ := Finset.mem_image.mp huS
  have hProd := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hb : x.1 < r := by
    have h := Finset.mem_range.mp hProd.1
    omega
  have ht : x.2 ≤ k := by
    have h := Finset.mem_range.mp hProd.2
    omega
  have hNumeric :
      hPosition k (q x.1) x.2 = hPosition k j k := by
    exact hxEq.symm.trans hjEq
  have hOriginal :=
    (hPosition_injective_bounded k (q x.1) x.2 j k
      ht le_rfl hNumeric).1
  have hAfter := hLater x.1 hb j hj
  omega

/-- Every real reserved-prefix numerical H copy, in EVERY generation,
has the precise ordinary L support bit toward EVERY selected top
original. Both orientations and all outside-support nonedges are
checked; one-target support is insufficient for this theorem.

The sort map tau labels NUMERICAL coordinates, so distinct selected
originals may have the same sort and still carry distinct positions.
-/
theorem finiteNumericH_ordered_prefix_all_top_support
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g : Nat) (q : Nat → Nat)
    (S : Finset Nat) (d : Nat)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (ha : a < r)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j)
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (q b) j = decide (tau (hPosition k j k) ∈ T)) :
    ∀ u ∈ orderedReservedNumericPrefix k q a g,
      ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          u w (0 : Fin 1) = decide (tau w ∈ T) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w u (0 : Fin 1) = decide (tau w ∈ T) := by
  classical
  intro u hu w hw
  obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨j,hj,hwj⟩ := Finset.mem_image.mp hw
  have hProd := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hb : x.1 < r := by
    have h := Finset.mem_range.mp hProd.1
    omega
  have ht : x.2 ≤ k := by
    have h := Finset.mem_range.mp hProd.2
    omega
  have hEarlier : q x.1 < j := hLater x.1 hb j hj
  have hForward :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (orderedReservedNumericPos k q x) (hPosition k j k)
        (0 : Fin 1) = E (q x.1) j := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k (q x.1) x.2) (hPosition k j k)
      (0 : Fin 1) = E (q x.1) j
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k (q x.1) j x.2
      (0 : Fin 1) hEarlier ht
  have hReverse :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k j k) (orderedReservedNumericPos k q x)
        (0 : Fin 1) = E (q x.1) j := by
    have hSwap := henson_finiteNumericH_binary_symmetric
      E hSym k M (hPosition k j k)
        (orderedReservedNumericPos k q x)
    exact hSwap.trans hForward
  have hOriginal : E (q x.1) j =
      decide (tau (hPosition k j k) ∈ T) :=
    hUniform x.1 hb j hj
  rw [← hxu, ← hwj]
  exact ⟨hForward.trans hOriginal,
    hReverse.trans hOriginal⟩

/-- Physical selected top copies actually lie in the finite numerical
carrier, provided their literal numerical coordinates lie below M.
Merely specifying original indices without this bound is not enough. -/
theorem numericHTopPool_mem_finiteH_of_cut
    (E : Nat → Nat → Bool) (k M : Nat)
    (S : Finset Nat)
    (hTop : ∀ j ∈ S, hPosition k j k < M) :
    ∀ w ∈ numericHTopPool k S,
      w ∈ (finiteNumericHL (normalizedGraphModel E) k M).carrier := by
  intro w hw
  obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hw
  change w < M
  rw [heq]
  exact hTop j hj

/-- Conditional physical marked-front age with a nonconsecutive
reserved block and the top-coordinate entire-front support column
DERIVED from simultaneous original E columns.

All additional old-reserved isolation, gap-to-future zeros,
whole-past K-free test and independent old-age reference table
hypotheses remain explicit. This does NOT assert their existence. -/
theorem finiteNumericH_ordered_top_marked_front_age_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g ell d : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (S : Finset Nat)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (q b) j = decide (tau (hPosition k j k) ∈ T))
    (c : Nat → Fin d → Bool)
    (P G : Finset Nat)
    (hNoPQ : ∀ p ∈ P, ∀ u ∈ orderedReservedNumericPrefix k q a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p u (0 : Fin 1) = false)
    (hNoGW : ∀ z ∈ G, ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z w (0 : Fin 1) = false)
    (hPast : finitePoolCliqueCheck
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        ell ((P ∪ orderedReservedNumericPrefix k q a g) ∪ G) = false)
    (hOld : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p p' (0 : Fin 1) = A p p')
    (hFuture : ∀ w ∈ numericHTopPool k S,
        ∀ w' ∈ numericHTopPool k S, w ≠ w' →
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w w' (0 : Fin 1) = A w w')
    (hPhysicalColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p w (0 : Fin 1) = c p (tau w) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w p (0 : Fin 1) = c p (tau w))
    (hReferenceColumns : ∀ p ∈ P, ∀ w ∈ numericHTopPool k S,
        A p w = c p (tau w) ∧ A w p = c p (tau w)) :
    finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (((P ∪ orderedReservedNumericPrefix k q a g) ∪ G) ∪
        numericHTopPool k S) = false ↔
    finitePoolCliqueCheck A ell (P ∪ numericHTopPool k S) = false ∧
      (if g < a then a else a+1) +
        finiteDirectedCliqueCapacity
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1))
          (markedSupportPool d (numericHTopPool k S) tau T) < ell := by
  exact finiteNumericH_ordered_marked_front_prefix_age_iff
    E A hSym k M r a g ell d q ha hr hgk hOrder hClique
    tau T c P G (numericHTopPool k S)
    (orderedReservedNumericPrefix_disjoint_topPool
      k r a g q S ha hLater)
    hNoPQ hNoGW
    (finiteNumericH_ordered_prefix_all_top_support
      E hSym k M r a g q S d tau T ha hLater hUniform)
    hPast hOld hFuture hPhysicalColumns hReferenceColumns

#print axioms Kk.orderedReservedNumericPrefix_disjoint_topPool
#print axioms Kk.finiteNumericH_ordered_prefix_all_top_support
#print axioms Kk.numericHTopPool_mem_finiteH_of_cut
#print axioms Kk.finiteNumericH_ordered_top_marked_front_age_iff

end Kk
