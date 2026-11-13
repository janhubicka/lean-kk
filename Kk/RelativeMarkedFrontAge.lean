import Kk.FiniteCliqueEmbeddingTransport
import Kk.NumericHReservedPrefixCapacity
import Mathlib.Tactic

/-!
# KK Track A: complete marked-front finite age bridge (ordinary L)

The precise English theorem and hostile audit were committed FIRST:
  docs/relative_marked_front_age_english_audit.md

A finite future W may contain any number of vertices of each marked
sort. Every old/future column is fixed by a typed lookup and is checked
in BOTH orientations. Every reserved/future column is the selected
support bit, including zero bits outside that support. Internal future
edges remain arbitrary but must agree with the reference age table.

This is an exact CONDITIONAL finite graph-L gluing equivalence. It does
not construct the relative physical Henson stage, extend a particular
fixed ambient prefix with every abstract feasible clique, or identify
auxiliary Kpt E / B3 / a common labelled source.
-/

namespace Kk

open SuccessorTree.V10

/-- The marked vertices whose sorts belong to the reserved support.
There may be arbitrarily many vertices of the same sort. -/
def markedSupportPool (d : Nat) (W : Finset Nat)
    (tau : Nat → Fin d) (T : Finset (Fin d)) : Finset Nat :=
  W.filter (fun w => tau w ∈ T)

/-- Exact off-diagonal graph agreement on a finite pool transports the
full directed finite clique test, including the threshold-zero case.
This is a specialization of the previously verified induced-image
transport along the identity map. -/
theorem finitePoolCliqueCheck_false_iff_reference
    (L A : Nat → Nat → Bool) (ell : Nat) (V : Finset Nat)
    (hAgree : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → L x y = A x y) :
    finitePoolCliqueCheck L ell V = false ↔
      finitePoolCliqueCheck A ell V = false := by
  have hInj : Set.InjOn (fun x : Nat => x) ↑V := by
    intro x _ y _ h
    exact h
  have hTransport := finitePoolCliqueCheck_false_iff_induced_image
    L A V (fun x : Nat => x) hInj hAgree ell
  simpa using hTransport

/-- Exact all-marked-sort finite continuation criterion.

The reference graph A is the independently prescribed old-continuation
table: both L and A use the SAME actual typed columns c(p,tau(w)) on
every P-W pair in both directions, and agree on old-old and
future-future off-diagonal atoms.

The reserve Q sees every marked w in both directions iff tau(w) lies
in the support T; no target is singled out. The gap pool G sees none
of W, and the entire displayed past must already be K_ell-free.

The conclusion uses the ACTUAL clique capacity of the supported
future pool, not its cardinality; neither Q nor W_T need be cliques.
-/
theorem finite_marked_front_gluing_iff_reference
    (L A : Nat → Nat → Bool) (ell d : Nat)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool)
    (P Q G W : Finset Nat)
    (hDisjoint : Disjoint Q W)
    (hNoPQ : ∀ p ∈ P, ∀ q ∈ Q, L p q = false)
    (hNoGW : ∀ z ∈ G, ∀ w ∈ W, L z w = false)
    (hSupport : ∀ q ∈ Q, ∀ w ∈ W,
        L q w = decide (tau w ∈ T) ∧
        L w q = decide (tau w ∈ T))
    (hPast : finitePoolCliqueCheck L ell ((P ∪ Q) ∪ G) = false)
    (hOld : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → L p p' = A p p')
    (hFuture : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
        L w w' = A w w')
    (hPhysicalColumns : ∀ p ∈ P, ∀ w ∈ W,
        L p w = c p (tau w) ∧ L w p = c p (tau w))
    (hReferenceColumns : ∀ p ∈ P, ∀ w ∈ W,
        A p w = c p (tau w) ∧ A w p = c p (tau w)) :
    finitePoolCliqueCheck L ell (((P ∪ Q) ∪ G) ∪ W) = false ↔
      finitePoolCliqueCheck A ell (P ∪ W) = false ∧
        finiteDirectedCliqueCapacity L Q +
          finiteDirectedCliqueCapacity L
            (markedSupportPool d W tau T) < ell := by
  classical
  have hU : markedSupportPool d W tau T ⊆ W := by
    exact Finset.filter_subset _ _
  have hQU : Disjoint Q (markedSupportPool d W tau T) := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxU
    exact (Finset.disjoint_left.mp hDisjoint) hxQ
      (Finset.mem_filter.mp hxU).1
  have hFullSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        L q w = decide (w ∈ markedSupportPool d W tau T) ∧
        L w q = decide (w ∈ markedSupportPool d W tau T) := by
    intro q hq w hw
    have hDec : decide (w ∈ markedSupportPool d W tau T) =
        decide (tau w ∈ T) := by
      simp [markedSupportPool, hw]
    rw [hDec]
    exact hSupport q hq w hw
  have hBase := finitePoolCliqueCheck_isolated_block_gluing_iff
    L ell P Q G W (markedSupportPool d W tau T)
    hQU hU hNoPQ hNoGW hFullSupport hPast
  have hAgreement :
      ∀ x ∈ P ∪ W, ∀ y ∈ P ∪ W, x ≠ y → L x y = A x y := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxP | hxW
    · rcases Finset.mem_union.mp hy with hyP | hyW
      · exact hOld x hxP y hyP hxy
      · exact (hPhysicalColumns x hxP y hyW).1.trans
          (hReferenceColumns x hxP y hyW).1.symm
    · rcases Finset.mem_union.mp hy with hyP | hyW
      · exact (hPhysicalColumns y hyP x hxW).2.trans
          (hReferenceColumns y hyP x hxW).2.symm
      · exact hFuture x hxW y hyW hxy
  have hRef := finitePoolCliqueCheck_false_iff_reference
    L A ell (P ∪ W) hAgreement
  constructor
  · intro hFree
    obtain ⟨hBefore, hBudget⟩ := hBase.mp hFree
    exact ⟨hRef.mp hBefore, hBudget⟩
  · rintro ⟨hBefore, hBudget⟩
    exact hBase.mpr ⟨hRef.mpr hBefore, hBudget⟩

/-- The actual (consecutive-original) numerical-H L specialization.
The entire W is marked, including additional sorts outside T.
No source of the full physical columns is concealed: the complete
support and typed-old-column premises are explicit. -/
theorem finiteNumericH_marked_front_prefix_age_iff
    (E A : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g ell d : Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hClique : ∀ b c, b < c → c < r → E (N+b) (N+c) = true)
    (tau : Nat → Fin d) (T : Finset (Fin d))
    (c : Nat → Fin d → Bool)
    (P G W : Finset Nat)
    (hDisjoint : Disjoint (reservedBlockNumericPrefix k N a g) W)
    (hNoPQ : ∀ p ∈ P, ∀ q ∈ reservedBlockNumericPrefix k N a g,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          p q (0 : Fin 1) = false)
    (hNoGW : ∀ z ∈ G, ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          z w (0 : Fin 1) = false)
    (hSupport : ∀ q ∈ reservedBlockNumericPrefix k N a g,
      ∀ w ∈ W,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          q w (0 : Fin 1) = decide (tau w ∈ T) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w q (0 : Fin 1) = decide (tau w ∈ T))
    (hPast : finitePoolCliqueCheck
        (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
          u v (0 : Fin 1))
        ell ((P ∪ reservedBlockNumericPrefix k N a g) ∪ G) = false)
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
      ell (((P ∪ reservedBlockNumericPrefix k N a g) ∪ G) ∪ W) = false ↔
    finitePoolCliqueCheck A ell (P ∪ W) = false ∧
      (if g < a then a else a+1) +
        finiteDirectedCliqueCapacity
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1))
          (markedSupportPool d W tau T) < ell := by
  have hResult := finite_marked_front_gluing_iff_reference
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    A ell d tau T c P (reservedBlockNumericPrefix k N a g) G W
    hDisjoint hNoPQ hNoGW hSupport hPast hOld hFuture
    hPhysicalColumns hReferenceColumns
  rw [finiteNumericH_reserved_block_prefix_capacity
    E hSym k N M r a g ha hr hgk hClique] at hResult
  exact hResult

/-- Named K3 P4 hostile regression:
original labels p=0,q=1,y=2,x=3 with edges p-y,y-q,q-x.
The one-target q-x support bit is true, but the additional marked
outside-support q-y bit is also true and violates the complete-front
support-zero hypothesis. -/
def trackAP4OriginalEdge (i j : Nat) : Bool :=
  decide ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
          (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))

theorem trackAP4_one_target_not_whole_front :
    trackAP4OriginalEdge 1 3 = true ∧
    trackAP4OriginalEdge 1 2 = true ∧
    trackAP4OriginalEdge 1 2 ≠
      decide ((2 : Nat) ∈ ({3} : Finset Nat)) := by
  decide

#print axioms finitePoolCliqueCheck_false_iff_reference
#print axioms finite_marked_front_gluing_iff_reference
#print axioms finiteNumericH_marked_front_prefix_age_iff
#print axioms trackAP4_one_target_not_whole_front

end Kk
