import Kk.ArbitraryWitnessGluing
import Kk.UniversalFutureDisjointCliques
import Kk.FiniteCliqueIntegerWitness
import Mathlib.Tactic

/-!
# Sharp ordinary-L raw support-block budget and relative four-pool certificate

English proof and hostile audit were committed first in
  docs/raw_support_block_budget_english_audit.md

For raw B(T), a reserved block with exact clique capacity
a = ell-1-B(T) (Nat truncated subtraction) cannot form an ell-clique
with any future clique having support size <=B(T) and total size <ell.

The actual four-pool corollary explicitly retains all old/reserved,
gap/future and BOTH support-direction L columns plus separate complete
past and old-plus-future forbidden-clique tests. It proves a relative
certificate IF an appropriate Nat-indexed L table already exists:
it does not construct that table, numerical H+ Kpt E closure, or
the common labelled inverse-source orbit.
-/

namespace Kk

/-- The essential arithmetic of an auxiliary reserved clique block.
Natural subtraction is TRUNCATED. For b>=ell-1, the block is empty,
and the independent strict n<ell premise cannot be dropped. -/
theorem rawSupportBlock_add_clique_below
    (ell b n : Nat) (hell : 0 < ell)
    (hBound : n ≤ b) (hSmall : n < ell) :
    (ell - 1 - b) + n < ell := by
  omega

/-- The one verified finite universal L-future has a safe prescribed
reserved-block budget on every support T, against EVERY directed
clique subset s. We do not assume the filtered set of all T-vertices
in the whole future is itself a clique. -/
theorem universalWitnessFuture_raw_support_block_budget
    (d ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (s : Finset (UniversalWitnessVertex d ell))
    (hSub : s ⊆ universalWitnessFuture d ell B)
    (hClique : IsUniversalWitnessClique s) :
    (ell - 1 - B T) +
      (s.filter (fun v => v.2.1 ∈ T.1)).card < ell := by
  classical
  have hRaw :=
    universalWitnessFuture_clique_respects_raw
      d ell hell B s hSub hClique T
  have hSmall :=
    universalWitnessFuture_clique_card_lt
      d ell hell B s hSub hClique
  have hFilter :
      (s.filter (fun v => v.2.1 ∈ T.1)).card < ell :=
    lt_of_le_of_lt
      (Finset.card_le_card (Finset.filter_subset _ _)) hSmall
  exact rawSupportBlock_add_clique_below ell (B T)
    (s.filter (fun v => v.2.1 ∈ T.1)).card
    hell hRaw hFilter

/-- Sufficient ACTUAL four-pool K_ell-free certificate when the
reserved Q has the precise raw-bound clique CAPACITY ell-1-B(T)
and EVERY directed future clique respects B(T).

This uses the full genuine Nat-indexed finite L edge table and
the preexisting exact four-pool gluing theorem. It does not
assume that W_T or W itself is a complete clique. Nor does it
infer required Q/W L columns or full Kpt parameter closure from B. -/
theorem finitePoolCliqueCheck_gluing_of_raw_support_bound
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 0 < ell)
    (B : IntegerGraphSupport d ell → Nat)
    (T : IntegerGraphSupport d ell)
    (P Q G W : Finset Nat)
    (sort : Nat → Fin d)
    (hCapacity :
      finiteDirectedCliqueCapacity E Q = ell - 1 - B T)
    (hQU :
      Disjoint Q (W.filter (fun w => sort w ∈ T.1)))
    (hNoPQ :
      ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (hNoGW :
      ∀ z ∈ G, ∀ w ∈ W, E z w = false)
    (hSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        E q w = decide (sort w ∈ T.1) ∧
        E w q = decide (sort w ∈ T.1))
    (hPast :
      finitePoolCliqueCheck E ell ((P ∪ Q) ∪ G) = false)
    (hOldFuture :
      finitePoolCliqueCheck E ell (P ∪ W) = false)
    (hRaw :
      ∀ s : Finset Nat, s ⊆ W → IsDirectedCliqueOn E s →
        (s.filter (fun w => sort w ∈ T.1)).card ≤ B T) :
    finitePoolCliqueCheck E ell (((P ∪ Q) ∪ G) ∪ W) = false := by
  classical
  apply (finitePoolCliqueCheck_gluing_all_support_witnesses
    E ell P Q G W sort T.1 hQU hNoPQ hNoGW hSupport hPast).2
  refine ⟨hOldFuture, ?_⟩
  intro s hsW hsClique
  rw [hCapacity]
  have hWFree :=
    finitePoolCliqueCheck_oldFuture_implies_future_false
      E ell P W hOldFuture
  have hSmall :=
    finiteClique_card_lt_of_pool_cliqueFree
      E ell W s hWFree hsW hsClique
  have hFilter :
      (s.filter (fun w => sort w ∈ T.1)).card < ell :=
    lt_of_le_of_lt
      (Finset.card_le_card (Finset.filter_subset _ _)) hSmall
  exact rawSupportBlock_add_clique_below ell (B T)
    (s.filter (fun w => sort w ∈ T.1)).card
    hell (hRaw s hsW hsClique) hFilter

#print axioms rawSupportBlock_add_clique_below
#print axioms universalWitnessFuture_raw_support_block_budget
#print axioms finitePoolCliqueCheck_gluing_of_raw_support_bound

end Kk
