import Kk.HBlockClique

/-!
# Selected-future support of an H clique meeting a reserved block

A canonical witness block is assigned a selected active support.
An original vertex reserved for that block is made nonadjacent to
selected future originals outside this support.

Because the genuine H construction never introduces a binary atom
absent between the corresponding original vertices, its generation
copies can only meet selected future vertices from that support
inside a positive clique.

Together with the verified nonadjacency of distinct witness blocks,
this gives a concrete *block-locality* statement for cliques of
actual reserved H vertices and selected future H vertices.

This is NOT the whole corrected (B3) projection. The full age test
quantifies over arbitrary L-only continuation witnesses, whose
auxiliary parameter types must separately be matched to the
designated reserved blocks or shown harmless.
-/

namespace Kk

open SuccessorTree.V10

/-- An H relation from a reserved original to a selected future
original implies that the selected label belongs to the
reserved block's prescribed active support. All generations are
covered, not only the selected top generation. -/
theorem reserved_H_aux_selected_clique_support
    (K : AgeTestModel 1 0 1)
    (k M P B Q : Nat)
    (original : Fin M → Nat)
    (block : Fin M → Fin B)
    (auxOrigin : Fin P → Fin M)
    (auxGeneration : Fin P → Nat)
    (selectedOriginal : Fin Q → Nat)
    (selectedGeneration : Fin Q → Nat)
    (support : Fin B → Fin Q → Prop)
    (hBefore : ∀ a t, original (auxOrigin a) < selectedOriginal t)
    (hAuxGeneration : ∀ a, auxGeneration a ≤ k)
    (hSelectedGeneration : ∀ t, selectedGeneration t ≤ k)
    (hOutside : ∀ i t, ¬ support (block i) t →
      K.binary (original i) (selectedOriginal t) (0 : Fin 1) = false)
    (hMixedEdges : ∀ a t,
      (infiniteNumericHL K k).binary
        (hPosition k (original (auxOrigin a)) (auxGeneration a))
        (hPosition k (selectedOriginal t) (selectedGeneration t))
        (0 : Fin 1) = true) :
    ∀ a t, support (block (auxOrigin a)) t := by
  intro a t
  by_contra hBad
  have hMissing :=
    numericH_preserves_original_nonedge K k
      (original (auxOrigin a)) (selectedOriginal t)
      (auxGeneration a) (selectedGeneration t)
      (hBefore a t) (hAuxGeneration a) (hSelectedGeneration t)
      (fun r => by
        fin_cases r
        exact hOutside (auxOrigin a) t hBad)
      (0 : Fin 1)
  have hEdge := hMixedEdges a t
  rw [hMissing] at hEdge
  cases hEdge

/-- A clique of reserved auxiliary H copies, together with any
selected-future H vertices adjacent to all of them, uses only
ONE reserved block, and every selected-future label lies in that
block's prescribed support.

A distinguished auxiliary a0 witnesses which block is used.
No unqualified parameter-closed (B3) assertion is inferred. -/
theorem reserved_H_clique_one_block_and_selected_support
    (K : AgeTestModel 1 0 1)
    (k M P B Q : Nat)
    (original : Fin M → Nat)
    (hOriginal : StrictMono original)
    (block : Fin M → Fin B)
    (auxOrigin : Fin P → Fin M)
    (auxGeneration : Fin P → Nat)
    (selectedOriginal : Fin Q → Nat)
    (selectedGeneration : Fin Q → Nat)
    (support : Fin B → Fin Q → Prop)
    (a0 : Fin P)
    (hAuxGeneration : ∀ a, auxGeneration a ≤ k)
    (hSelectedGeneration : ∀ t, selectedGeneration t ≤ k)
    (hNonedge : ∀ i j : Fin M, i < j →
      block i ≠ block j →
      K.binary (original i) (original j) (0 : Fin 1) = false)
    (hBefore : ∀ a t, original (auxOrigin a) < selectedOriginal t)
    (hOutside : ∀ i t, ¬ support (block i) t →
      K.binary (original i) (selectedOriginal t) (0 : Fin 1) = false)
    (hAuxClique : ∀ a b : Fin P, a ≠ b →
      (infiniteNumericHL K k).binary
        (hPosition k (original (auxOrigin a)) (auxGeneration a))
        (hPosition k (original (auxOrigin b)) (auxGeneration b))
        (0 : Fin 1) = true)
    (hMixedEdges : ∀ a t,
      (infiniteNumericHL K k).binary
        (hPosition k (original (auxOrigin a)) (auxGeneration a))
        (hPosition k (selectedOriginal t) (selectedGeneration t))
        (0 : Fin 1) = true) :
    (∀ a, block (auxOrigin a) = block (auxOrigin a0)) ∧
      (∀ t, support (block (auxOrigin a0)) t) := by
  have hOne :=
    reserved_H_clique_one_block K k M P B
      original hOriginal block auxOrigin auxGeneration
      hAuxGeneration hNonedge hAuxClique
  have hSupported :=
    reserved_H_aux_selected_clique_support K
      k M P B Q original block auxOrigin auxGeneration
      selectedOriginal selectedGeneration support hBefore
      hAuxGeneration hSelectedGeneration hOutside hMixedEdges
  refine ⟨(fun a => hOne a a0), ?_⟩
  intro t
  exact hSupported a0 t

end Kk
