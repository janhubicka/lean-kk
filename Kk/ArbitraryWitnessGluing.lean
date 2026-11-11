import Kk.FiniteCliqueSupportWitness
import Kk.NumericHReservedPrefixGluing
import Mathlib.Tactic

/-!
# Exact four-pool gluing as bounds on ALL hypothetical clique witnesses

English proof and hostile audit were committed first in
\`docs/arbitrary_witness_gluing_english_audit.md\`.

Unlike the previous realized selected-top column lemma, this theorem
quantifies over every directed clique inside ANY finite future graph W.
Its old-plus-future and entire-past clique tests remain explicit;
it does not assume that every hypothetical W is realized in Henson
or solve the auxiliary parameter-closed B3 source matching.
-/

namespace Kk

open SuccessorTree.V10

/-- Exact four-pool gluing iff, with the clique budget expressed against
EVERY possible supported clique witness inside arbitrary W. The supported
pool U is the actual sort filter, not a separate chosen finite set. -/
theorem finitePoolCliqueCheck_gluing_all_support_witnesses
    {d : Nat} (E : Nat → Nat → Bool) (ell : Nat)
    (P Q G W : Finset Nat)
    (sort : Nat → Fin d) (T : Finset (Fin d))
    (hQU : Disjoint Q (W.filter (fun w => sort w ∈ T)))
    (hNoPQ :
      ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (hNoGW :
      ∀ z ∈ G, ∀ w ∈ W, E z w = false)
    (hSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        E q w = decide (sort w ∈ T) ∧
        E w q = decide (sort w ∈ T))
    (hPast :
      finitePoolCliqueCheck E ell ((P ∪ Q) ∪ G) = false) :
    finitePoolCliqueCheck E ell (((P ∪ Q) ∪ G) ∪ W) = false ↔
      finitePoolCliqueCheck E ell (P ∪ W) = false ∧
      ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        finiteDirectedCliqueCapacity E Q +
          (s.filter (fun w => sort w ∈ T)).card < ell := by
  classical
  let U : Finset Nat := W.filter (fun w => sort w ∈ T)
  have hU : U ⊆ W := Finset.filter_subset _ _
  have hFullSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        E q w = decide (w ∈ U) ∧
        E w q = decide (w ∈ U) := by
    intro q hq w hw
    have hMembership : w ∈ U ↔ sort w ∈ T := by
      simp [U, hw]
    have hDec : decide (w ∈ U) = decide (sort w ∈ T) := by
      by_cases hIn : sort w ∈ T
      · have hImage := hMembership.mpr hIn
        simp [hImage,hIn]
      · have hNoImage : w ∉ U := by
          intro h
          exact hIn (hMembership.mp h)
        simp [hNoImage,hIn]
    obtain ⟨hF,hR⟩ := hSupport q hq w hw
    exact ⟨hF.trans hDec.symm, hR.trans hDec.symm⟩
  have hGluing := finitePoolCliqueCheck_isolated_block_gluing_iff
    E ell P Q G W U hQU hU hNoPQ hNoGW hFullSupport hPast
  have hWitness := finiteCliqueSupportCapacity_iff_all_witnesses
    E W sort T (finiteDirectedCliqueCapacity E Q) ell
  constructor
  · intro hFull
    obtain ⟨hOld,hBudget⟩ := hGluing.mp hFull
    exact ⟨hOld,hWitness.mp hBudget⟩
  · rintro ⟨hOld,hAll⟩
    exact hGluing.mpr ⟨hOld,hWitness.mpr hAll⟩

/-- Physical numerical-H version with the exact reserved-prefix capacity
a (if g<a) or a+1 (if g>=a), again against ALL arbitrary finite future
clique witnesses. All ordinary-L support columns are explicit hypotheses,
not consequences of the actual selected-top realizations. -/
theorem finiteNumericH_reserved_prefix_gluing_all_support_witnesses
    {d : Nat}
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g ell : Nat)
    (ha : a < r) (hr : r ≤ k+1) (hgk : g ≤ k)
    (hClique : ∀ b c, b < c → c < r → E (N+b) (N+c) = true)
    (P G W : Finset Nat)
    (sort : Nat → Fin d) (T : Finset (Fin d))
    (hQU :
      Disjoint (reservedBlockNumericPrefix k N a g)
        (W.filter (fun w => sort w ∈ T)))
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
          q w (0 : Fin 1) = decide (sort w ∈ T) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w q (0 : Fin 1) = decide (sort w ∈ T))
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
      ∀ s : Finset Nat, s ⊆ W →
        IsDirectedCliqueOn
          (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
            u v (0 : Fin 1)) s →
        (if g < a then a else a+1) +
          (s.filter (fun w => sort w ∈ T)).card < ell := by
  have hGeneric := finitePoolCliqueCheck_gluing_all_support_witnesses
    (fun u v => (finiteNumericHL (normalizedGraphModel E) k M).binary
      u v (0 : Fin 1))
    ell P (reservedBlockNumericPrefix k N a g) G W sort T
    hQU hNoPQ hNoGW hSupport hPast
  have hPhysical := finiteNumericH_reserved_block_prefix_capacity
    E hSym k N M r a g ha hr hgk hClique
  rw [hPhysical] at hGeneric
  exact hGeneric

#print axioms finitePoolCliqueCheck_gluing_all_support_witnesses
#print axioms finiteNumericH_reserved_prefix_gluing_all_support_witnesses

end Kk
