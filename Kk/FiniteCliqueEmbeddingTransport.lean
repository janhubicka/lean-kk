import Kk.ReservedPrefixCapacity
import Kk.IsolatedBlockContinuationAge
import Mathlib.Tactic

/-!
# Exact finite directed-clique capacity transport along induced L embeddings

English proof and hostile audit committed BEFORE this Lean file:
  docs/finite_clique_embedding_transport_english_audit.md

An injective finite image with complete off-diagonal ordinary-L atom
agreement preserves exact directed clique capacity, and hence the
Boolean no-K_q checker at EVERY threshold q, including q=0.
No symmetry, loops, full ambient graph universality or auxiliary Kpt E
is assumed. This is the key safe-neighbour-set transfer needed before
applying the separately verified left-dense Henson one-point theorem.
-/

namespace Kk

/-- The exact finite directed clique capacity is invariant under a
finite injective *induced* map between arbitrary Boolean L tables.
Injectivity and complete equality of every ordered off-diagonal
binary atom are hypotheses; no global inverse map is assumed. -/
theorem finiteDirectedCliqueCapacity_induced_image_eq
    (A E : Nat → Nat → Bool)
    (P : Finset Nat) (f : Nat → Nat)
    (hInj : Set.InjOn f ↑P)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      A x y = E (f x) (f y)) :
    finiteDirectedCliqueCapacity E (P.image f) =
      finiteDirectedCliqueCapacity A P := by
  classical
  have hInjSub (s : Finset Nat) (hs : s ⊆ P) :
      Set.InjOn f ↑s := by
    intro x hx y hy hEq
    exact hInj (hs hx) (hs hy) hEq
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro t ht
    obtain ⟨htPow, htClique⟩ := Finset.mem_filter.mp ht
    have htSub : t ⊆ P.image f := Finset.mem_powerset.mp htPow
    let s : Finset Nat := P.filter (fun x => f x ∈ t)
    have hsSub : s ⊆ P := Finset.filter_subset _ _
    have hsImage : s.image f = t := by
      apply Finset.Subset.antisymm
      · intro z hz
        obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
        exact hxz ▸ (Finset.mem_filter.mp hx).2
      · intro z hz
        obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp (htSub hz)
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨hx, hxz ▸ hz⟩, hxz⟩
    have hsCard : s.card = t.card := by
      have hc := Finset.card_image_iff.mpr (hInjSub s hsSub)
      rw [hsImage] at hc
      exact hc.symm
    have hsClique : IsDirectedCliqueOn A s := by
      intro x hx y hy hxy
      have hxP : x ∈ P := hsSub hx
      have hyP : y ∈ P := hsSub hy
      have hxT : f x ∈ t := (Finset.mem_filter.mp hx).2
      have hyT : f y ∈ t := (Finset.mem_filter.mp hy).2
      have hfNe : f x ≠ f y := by
        intro heq
        exact hxy (hInj hxP hyP heq)
      have hPos : E (f x) (f y) = true :=
        htClique (f x) hxT (f y) hyT hfNe
      exact (hEdge x hxP y hyP hxy).trans hPos
    have hsBound : s.card ≤ finiteDirectedCliqueCapacity A P :=
      directedClique_card_le_capacity A P s hsSub hsClique
    rw [hsCard] at hsBound
    exact hsBound
  · apply Finset.sup_le
    intro s hs
    obtain ⟨hsPow, hsClique⟩ := Finset.mem_filter.mp hs
    have hsSub : s ⊆ P := Finset.mem_powerset.mp hsPow
    have htSub : s.image f ⊆ P.image f :=
      Finset.image_subset_image hsSub
    have htClique : IsDirectedCliqueOn E (s.image f) := by
      intro u hu v hv huv
      obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, hvy⟩ := Finset.mem_image.mp hv
      have hxy : x ≠ y := by
        intro hSame
        subst y
        exact huv (hux.symm.trans hvy)
      have hA : A x y = true := hsClique x hx y hy hxy
      have hE : E (f x) (f y) = true :=
        (hEdge x (hsSub hx) y (hsSub hy) hxy).symm.trans hA
      simpa only [hux,hvy] using hE
    have htBound : (s.image f).card ≤
        finiteDirectedCliqueCapacity E (P.image f) :=
      directedClique_card_le_capacity E (P.image f)
        (s.image f) htSub htClique
    have hsCard := Finset.card_image_iff.mpr (hInjSub s hsSub)
    rw [hsCard] at htBound
    exact htBound

/-- The exact Boolean finite K_q-free test is invariant under the
same finite induced map for EVERY threshold q, including q=0. -/
theorem finitePoolCliqueCheck_false_iff_induced_image
    (A E : Nat → Nat → Bool)
    (P : Finset Nat) (f : Nat → Nat)
    (hInj : Set.InjOn f ↑P)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      A x y = E (f x) (f y))
    (q : Nat) :
    finitePoolCliqueCheck A q P = false ↔
      finitePoolCliqueCheck E q (P.image f) = false := by
  have hCapacity :=
    finiteDirectedCliqueCapacity_induced_image_eq A E P f hInj hEdge
  constructor
  · intro hSafe
    apply (finitePoolCliqueCheck_false_iff_capacity_lt
      E q (P.image f)).2
    rw [hCapacity]
    exact (finitePoolCliqueCheck_false_iff_capacity_lt A q P).1
      hSafe
  · intro hSafe
    apply (finitePoolCliqueCheck_false_iff_capacity_lt A q P).2
    have hBound :=
      (finitePoolCliqueCheck_false_iff_capacity_lt
        E q (P.image f)).1 hSafe
    rw [hCapacity] at hBound
    exact hBound

/-- For strictly increasing enumerated partial embeddings the
finite injection needed for exact neighbourhood safety is automatic.
This is the interface to the chronological left-density construction. -/
theorem finitePoolCliqueCheck_false_iff_strictMono_image
    (A E : Nat → Nat → Bool)
    (P : Finset Nat) (f : Nat → Nat)
    (hStrict : StrictMono f)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      A x y = E (f x) (f y))
    (q : Nat) :
    finitePoolCliqueCheck A q P = false ↔
      finitePoolCliqueCheck E q (P.image f) = false := by
  apply finitePoolCliqueCheck_false_iff_induced_image
    A E P f
  · intro x hx y hy heq
    exact hStrict.injective heq
  · exact hEdge

#print axioms finiteDirectedCliqueCapacity_induced_image_eq
#print axioms finitePoolCliqueCheck_false_iff_induced_image
#print axioms finitePoolCliqueCheck_false_iff_strictMono_image

end Kk
