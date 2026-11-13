import Kk.NumericPrefixGapZero
import Kk.OrderedTopMarkedSupport
import Mathlib.Tactic

/-!
# Track A: exact all-coordinate physical numerical-H prefix age

English proof and adversarial audit were committed FIRST in
  docs/numeric_prefix_gap_zero_english_audit.md

We take the actual numerical prefix [0, iota(q(a),g)+1), not an
unverified selected subset. Every coordinate belongs to old pool P,
the complete nonconsecutive reserved real-copy prefix Q, or its
literal complement G. All G-to-marked-top zeros follow from the
original-graph no-edge certificate for real gap coordinates, together
with the derived real-or-odd partition and exact H binary relations.

This is still a conditional finite result: the actual recursive
schedule's original gap-zero certificates, old/reserved isolation,
and reference integer-age identification are NOT inferred.
-/

namespace Kk

open SuccessorTree.V10

/-- Complete actual numerical-prefix (all-coordinate, including odd
dummies) selected-front age criterion with a nonconsecutive reserved
block and every future selected original represented at top generation.

The previous conditional gluing theorem's NUMERICAL gap-zero hypothesis
has been completely discharged: here only the explicit ORIGINAL
gap-to-selected zero-neighbourhood certificate remains, matching the
data required from the recursive original stage (Track B). The full
P union Q union G is **definitionally the entire numeric prefix**.

The reference A table still supplies full old-to-future sort columns
and internal future edges; no arbitrary abstract feasible W is claimed
to attach physically over a fixed incompatible past. -/
theorem finiteNumericH_ordered_whole_prefix_marked_age_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k M r a g ell d : Nat) (q : Nat → Nat)
    (ha : a < r) (hr : r ≤ k + 1) (hgk : g ≤ k)
    (hOrder : ∀ b c, b < c → c < r → q b < q c)
    (hClique : ∀ b c, b < c → c < r → E (q b) (q c) = true)
    (S : Finset Nat)
    (hLater : ∀ b, b < r → ∀ j ∈ S, q b < j)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (q b) j = decide (tau (hPosition k j k) ∈ T))
    (c : Nat → Fin d → Bool)
    (P : Finset Nat)
    (hP : ∀ p ∈ P, p < hPosition k (q a) g + 1)
    (hNoPQ : ∀ p ∈ P, ∀ u ∈ orderedReservedNumericPrefix k q a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p u (0 : Fin 1) = false)
    (hOriginalGapZeros : ∀ i t : Nat,
      t ≤ k →
      hPosition k i t ∈
        numericPrefixGapPool (hPosition k (q a) g + 1) P
          (orderedReservedNumericPrefix k q a g) →
      ∀ j ∈ S, E i j = false)
    (hPast : finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell (Finset.range (hPosition k (q a) g + 1)) = false)
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
      ell ((Finset.range (hPosition k (q a) g + 1)) ∪
        numericHTopPool k S) = false ↔
    finitePoolCliqueCheck A ell (P ∪ numericHTopPool k S) = false ∧
      (if g < a then a else a + 1) +
        finiteDirectedCliqueCapacity
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1))
          (markedSupportPool d (numericHTopPool k S) tau T) < ell := by
  classical
  let m : Nat := hPosition k (q a) g + 1
  let Q : Finset Nat := orderedReservedNumericPrefix k q a g
  let G : Finset Nat := numericPrefixGapPool m P Q
  have hPSub : P ⊆ Finset.range m := by
    intro p hp
    exact Finset.mem_range.mpr (hP p hp)
  have hQSub : Q ⊆ Finset.range m := by
    intro u hu
    have hCut : hPosition k (q a) g < m := by
      dsimp [m]
      omega
    have hWithin := orderedReservedNumericPrefix_inside_carrier
      k r a g m q ha hOrder hCut u hu
    exact Finset.mem_range.mpr hWithin
  have hFull : (P ∪ Q) ∪ G = Finset.range m :=
    numericPrefix_union_gap_exact m P Q hPSub hQSub
  have hGWithin : ∀ z ∈ G, z < m := by
    intro z hz
    have hzRange : z ∈ Finset.range m :=
      numericPrefixGapPool_subset_range m P Q hz
    exact Finset.mem_range.mp hzRange
  have hStart : ∀ j ∈ S, m ≤ hPosition k j 0 := by
    intro j hj
    exact orderedReserved_numeric_cut_before_all_selected
      k r a g q S ha hgk hLater j hj
  have hGOriginal : ∀ i t : Nat,
      t ≤ k → hPosition k i t ∈ G → ∀ j ∈ S, E i j = false := by
    intro i t ht hi j hj
    exact hOriginalGapZeros i t ht hi j hj
  have hNoGW : ∀ z ∈ G, ∀ w ∈ numericHTopPool k S,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        z w (0 : Fin 1) = false ∧
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        w z (0 : Fin 1) = false :=
    finiteNumericH_all_gap_to_marked_top_zero
      E hSym k M m G S hGWithin hStart hGOriginal
  have hNoGWForward : ∀ z ∈ G, ∀ w ∈ numericHTopPool k S,
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        z w (0 : Fin 1) = false := by
    intro z hz w hw
    exact (hNoGW z hz w hw).1
  have hPastPools : finitePoolCliqueCheck
      (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
        u v (0 : Fin 1))
      ell ((P ∪ Q) ∪ G) = false := by
    rw [hFull]
    exact hPast
  have hBridge := finiteNumericH_ordered_top_marked_front_age_iff
    E A hSym k M r a g ell d q ha hr hgk hOrder hClique
    S hLater tau T hUniform c P G
    hNoPQ hNoGWForward hPastPools hOld hFuture
    hPhysicalColumns hReferenceColumns
  rw [hFull] at hBridge
  exact hBridge

#print axioms Kk.finiteNumericH_ordered_whole_prefix_marked_age_iff

end Kk
