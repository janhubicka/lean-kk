import Kk.HBlockNonedges
import Kk.HensonEncoding
import Mathlib.Tactic

/-!
# Actual positive numerical-H edges of designated reserved gadgets

For a cover gadget, the reserved original vertices are strictly
increasing and are copied at numerical-H generations 0,1,...,r-1.
A later selected original is copied at the top generation k.

The genuine numerical-H binary relation is *gated*: positive original
edges need not survive every generation pairing. This module checks
the exact gate for the designated strictly increasing generation
sequence and its connection to a later top-generation vertex.

No abstract template binary relation is substituted for H. This
proves the positive L-edges of one designated gadget, not the
complete E/parameter-closed B3 age or the global resolved-copy
successor diary.
-/

namespace Kk

open SuccessorTree.V10

/-- Every positive original edge within a strictly increasing
reserved clique survives at its increasing designated H
generations a.val < b.val < r <= k. -/
theorem numericH_designated_reserved_pair_positive
    (E : Nat → Nat → Bool) (k r : Nat)
    (hr : r ≤ k)
    (original : Fin r ↪o Nat)
    (hBaseClique : ∀ a b : Fin r, a < b →
      E (original a) (original b) = true) :
    ∀ a b : Fin r, a < b →
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k (original a) a.val)
        (hPosition k (original b) b.val) (0 : Fin 1) = true := by
  intro a b hab
  have hq : a.val ≤ k := by have := a.isLt; omega
  have hm : b.val ≤ k := by have := b.isLt; omega
  have hGate : a.val < b.val := hab
  have hAtom :
      (normalizedGraphModel E).binary
        (original a) (original b) (0 : Fin 1) = true := by
    change E (original a) (original b) = true
    exact hBaseClique a b hab
  exact (hNumericBinary_real_forward_iff
    (normalizedGraphModel E).binary k
    (original a) (original b) a.val b.val (0 : Fin 1)
    (original.strictMono hab) hq hm).2
      ⟨Or.inl hGate, hAtom⟩

/-- Every positive original edge from a reserved original to
a LATER selected original survives at the selected top H
generation. Its reserved generation a.val is strictly below k. -/
theorem numericH_designated_reserved_to_top_positive
    (E : Nat → Nat → Bool) (k r : Nat)
    (hr : r ≤ k)
    (original : Fin r ↪o Nat) (selected : Nat)
    (hLater : ∀ a, original a < selected)
    (hJoined : ∀ a, E (original a) selected = true) :
    ∀ a : Fin r,
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k (original a) a.val)
        (hPosition k selected k) (0 : Fin 1) = true := by
  intro a
  have hq : a.val ≤ k := by have := a.isLt; omega
  have hGate : a.val < k := by have := a.isLt; omega
  have hAtom :
      (normalizedGraphModel E).binary
        (original a) selected (0 : Fin 1) = true := by
    change E (original a) selected = true
    exact hJoined a
  exact (hNumericBinary_real_forward_iff
    (normalizedGraphModel E).binary k
    (original a) selected a.val k (0 : Fin 1)
    (hLater a) hq le_rfl).2
      ⟨Or.inl hGate, hAtom⟩

/-- In the undirected K_ell graph language, each designated
reserved-to-selected top edge survives in both directed
orientations. No symmetry of numerical H is simply postulated;
it follows from the original graph's symmetry. -/
theorem numericH_designated_reserved_to_top_both
    (E : Nat → Nat → Bool) (k r : Nat)
    (hr : r ≤ k)
    (hSym : ∀ i j, E i j = E j i)
    (original : Fin r ↪o Nat) (selected : Nat)
    (hLater : ∀ a, original a < selected)
    (hJoined : ∀ a, E (original a) selected = true) :
    ∀ a : Fin r,
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k (original a) a.val)
        (hPosition k selected k) (0 : Fin 1) = true ∧
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k selected k)
        (hPosition k (original a) a.val) (0 : Fin 1) = true := by
  have hBaseSym : ∀ i j t,
      (normalizedGraphModel E).binary i j t =
        (normalizedGraphModel E).binary j i t := by
    intro i j t
    fin_cases t
    change E i j = E j i
    exact hSym i j
  intro a
  have hPositive :=
    numericH_designated_reserved_to_top_positive
      E k r hr original selected hLater hJoined a
  have hReverse := hNumericBinary_symmetric_of_base
    (normalizedGraphModel E).binary hBaseSym k
    (hPosition k selected k)
    (hPosition k (original a) a.val) (0 : Fin 1)
  exact ⟨hPositive, hReverse.trans hPositive⟩

/-- Turn an ACTUAL finite reserved clique S, enumerated in its
natural-number order, into a positive designated-generation
clique in the genuine numerical H structure. -/
theorem numericH_designated_clique_of_finite_set
    (E : Nat → Nat → Bool) (k r : Nat)
    (S : Finset Nat)
    (hCard : S.card = r)
    (hr : r ≤ k)
    (hClique : IsDirectedCliqueOn E S) :
    ∀ a b : Fin r, a < b →
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k (S.orderEmbOfFin hCard a) a.val)
        (hPosition k (S.orderEmbOfFin hCard b) b.val)
        (0 : Fin 1) = true := by
  let original : Fin r ↪o Nat := S.orderEmbOfFin hCard
  have hOriginal : ∀ a b : Fin r, a < b →
      E (original a) (original b) = true := by
    intro a b hab
    have ha : original a ∈ S := S.orderEmbOfFin_mem hCard a
    have hb : original b ∈ S := S.orderEmbOfFin_mem hCard b
    exact hClique (original a) ha (original b) hb
      (original.injective (ne_of_lt hab))
  exact numericH_designated_reserved_pair_positive
    E k r hr original hOriginal

end Kk
