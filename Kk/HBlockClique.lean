import Kk.HBlockNonedges
import Mathlib.Tactic

/-!
# A clique of reserved auxiliary H vertices meets only one block

Canonical witness gadgets are built from finite reserved cliques of
original vertices. Different gadget blocks are chosen mutually
nonadjacent in the original K_ell-free graph. The checked numerical
H-copying lemma shows that nonedges persist at ALL generations.

Consequently any complete auxiliary clique in the actual numerical
H structure uses vertices from a single reserved block. The theorem
does not assert that all (B3) age witnesses consist only of these
reserved real vertices: selected future types, non-designated
auxiliary parameter types, and the E-closure remain a separate task.

No abstract graph-action or Ramsey assumption is introduced.
-/

namespace Kk

open SuccessorTree.V10

/-- If the original reserved blocks are mutually nonadjacent,
then every complete directed clique of real H copies of reserved
originals has ONE block index, regardless of generations.

A hypothetical clique may contain the same original more than
once; the conclusion does not need to exclude that separately.
The constructed H relation is checked in its true numerical form,
not a hand-defined block model. -/
theorem reserved_H_clique_one_block
    (K : AgeTestModel 1 0 1)
    (k m n B : Nat)
    (original : Fin m → Nat)
    (hOriginal : StrictMono original)
    (block : Fin m → Fin B)
    (origin : Fin n → Fin m)
    (generation : Fin n → Nat)
    (hGeneration : ∀ a, generation a ≤ k)
    (hNonedge : ∀ i j : Fin m, i < j →
      block i ≠ block j →
      K.binary (original i) (original j) (0 : Fin 1) = false)
    (hClique : ∀ a b : Fin n, a ≠ b →
      (infiniteNumericHL K k).binary
        (hPosition k (original (origin a)) (generation a))
        (hPosition k (original (origin b)) (generation b))
        (0 : Fin 1) = true) :
    ∀ a b : Fin n, block (origin a) = block (origin b) := by
  intro a b
  by_contra hDifferent
  have hOriginsDifferent : origin a ≠ origin b := by
    intro h
    exact hDifferent (congrArg block h)
  have hab : a ≠ b := by
    intro h
    exact hDifferent (congrArg (fun t => block (origin t)) h)
  rcases lt_or_gt_of_ne hOriginsDifferent with hlt | hgt
  · have hMissing :=
      numericH_preserves_original_nonedge K
        k (original (origin a)) (original (origin b))
        (generation a) (generation b)
        (hOriginal hlt) (hGeneration a) (hGeneration b)
        (fun t => by
          fin_cases t
          exact hNonedge (origin a) (origin b) hlt hDifferent)
        (0 : Fin 1)
    have hEdge := hClique a b hab
    rw [hMissing] at hEdge
    cases hEdge
  · have hMissing :=
      numericH_preserves_original_nonedge K
        k (original (origin b)) (original (origin a))
        (generation b) (generation a)
        (hOriginal hgt) (hGeneration b) (hGeneration a)
        (fun t => by
          fin_cases t
          exact hNonedge (origin b) (origin a) hgt hDifferent.symm)
        (0 : Fin 1)
    have hEdge := hClique b a hab.symm
    rw [hMissing] at hEdge
    cases hEdge

end Kk
