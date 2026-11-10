import Kk.NumericHReservedPrefixGluing
import Kk.NumericHFullSelectedColumn
import Mathlib.Tactic

/-!
# Genuine numerical-H reserved-prefix to selected-top support columns

The English proof and hostile audit were committed FIRST in
\`docs/numeric_h_selected_top_support_columns_english_audit.md\`.

A uniform original directed edge column to an arbitrary finite later
original pool S, with supported subset T, becomes the exact BOTH-DIRECTION
ordinary binary L column between every reserved real-copy prefix vertex
and every top-generation copy of S. The original uniform-support
hypothesis is explicitly retained; no Henson one-point existence,
corrected-B3 age, or auxiliary E closure is inferred.
-/

namespace Kk

open SuccessorTree.V10

/-- All genuinely selected future original labels are copied at the
literal top generation, with the actual numerical H coordinate map. -/
def numericHTopPool (k : Nat) (S : Finset Nat) : Finset Nat :=
  S.image (fun j => hPosition k j k)

/-- The top-generation coordinate map is injective on ALL natural
original labels. There is no extra original-index truncation. -/
theorem numericHTopPos_injective (k : Nat) :
    Function.Injective (fun j : Nat => hPosition k j k) := by
  intro i j hEq
  exact (hPosition_injective_bounded k i k j k le_rfl le_rfl hEq).1

/-- Exact membership equivalence for the image of a set of selected
top original labels; the converse needs injection, not mere mapping. -/
theorem numericHTopPool_mem_iff (k : Nat) (T : Finset Nat) (j : Nat) :
    hPosition k j k ∈ numericHTopPool k T ↔ j ∈ T := by
  classical
  constructor
  · intro h
    obtain ⟨j',hj',hEq⟩ := Finset.mem_image.mp h
    have hj : j' = j := numericHTopPos_injective k hEq
    exact hj ▸ hj'
  · intro h
    exact Finset.mem_image.mpr ⟨j,h,rfl⟩

/-- Supported future originals form a subset of all selected future
originals, including after applying the exact H top coordinate map. -/
theorem numericHTopPool_mono (k : Nat) (T S : Finset Nat)
    (hTS : T ⊆ S) :
    numericHTopPool k T ⊆ numericHTopPool k S := by
  exact Finset.image_subset_image hTS

/-- The actual reserved real-copy prefix and the top future pool are
disjoint when all original future labels follow the entire reserve block.
This is proved from hPosition bounded-generation INJECTION. -/
theorem reservedBlockNumericPrefix_disjoint_topPool
    (k N r a g : Nat) (S : Finset Nat)
    (ha : a < r)
    (hLater : ∀ j ∈ S, N+r ≤ j) :
    Disjoint (reservedBlockNumericPrefix k N a g)
      (numericHTopPool k S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u huQ huS
  obtain ⟨x,hx,hxEq⟩ := Finset.mem_image.mp huQ
  obtain ⟨j,hj,hjEq⟩ := Finset.mem_image.mp huS
  have hProd := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hb : x.1 ≤ a := by
    have h := Finset.mem_range.mp hProd.1
    omega
  have ht : x.2 ≤ k := by
    have h := Finset.mem_range.mp hProd.2
    omega
  have hNumerical :
      hPosition k (N+x.1) x.2 = hPosition k j k := by
    exact hxEq.trans hjEq.symm
  have hOriginal :=
    (hPosition_injective_bounded k (N+x.1) x.2 j k
      ht le_rfl hNumerical).1
  have hAfter := hLater j hj
  omega

/-- Exact symmetric numerical-H binary L support from EVERY real
reserved-prefix copy, at EVERY generation, to EVERY genuinely later
selected top copy. The required uniform ORIGINAL edge column is explicit.

In particular the supported top pool need NOT be a clique, and the
two directed H atoms are proved separately rather than assumed. -/
theorem finiteNumericH_reserved_prefix_top_support
    (E : Nat → Nat → Bool)
    (hSym : ∀ i j, E i j = E j i)
    (k N M r a g : Nat)
    (ha : a < r)
    (S T : Finset Nat)
    (hLater : ∀ j ∈ S, N+r ≤ j)
    (hUniform : ∀ b, b < r → ∀ j ∈ S,
      E (N+b) j = decide (j ∈ T)) :
    ∀ q ∈ reservedBlockNumericPrefix k N a g,
      ∀ w ∈ numericHTopPool k S,
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          q w (0 : Fin 1) =
          decide (w ∈ numericHTopPool k T) ∧
        (finiteNumericHL (normalizedGraphModel E) k M).binary
          w q (0 : Fin 1) =
          decide (w ∈ numericHTopPool k T) := by
  classical
  intro q hq w hw
  obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
  obtain ⟨j,hj,hwj⟩ := Finset.mem_image.mp hw
  have hProd := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hb : x.1 < r := by
    have h := Finset.mem_range.mp hProd.1
    omega
  have ht : x.2 ≤ k := by
    have h := Finset.mem_range.mp hProd.2
    omega
  have hEarlier : N+x.1 < j := by
    have hAfter := hLater j hj
    omega
  have hForward :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (reservedBlockNumericPos k N x) (hPosition k j k)
        (0 : Fin 1) = E (N+x.1) j := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k (N+x.1) x.2) (hPosition k j k) (0 : Fin 1) =
      E (N+x.1) j
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k (N+x.1) j x.2
      (0 : Fin 1) hEarlier ht
  have hReverse :
      (finiteNumericHL (normalizedGraphModel E) k M).binary
        (hPosition k j k) (reservedBlockNumericPos k N x)
        (0 : Fin 1) = E (N+x.1) j := by
    have hSwap := henson_finiteNumericH_binary_symmetric
      E hSym k M (hPosition k j k) (reservedBlockNumericPos k N x)
    exact hSwap.trans hForward
  have hOriginal : E (N+x.1) j = decide (j ∈ T) :=
    hUniform x.1 hb j hj
  have hSelected : hPosition k j k ∈ numericHTopPool k T ↔
      j ∈ T := numericHTopPool_mem_iff k T j
  have hDec :
      decide (hPosition k j k ∈ numericHTopPool k T) =
        decide (j ∈ T) := by
    by_cases hIn : j ∈ T
    · have hImage : hPosition k j k ∈ numericHTopPool k T :=
        hSelected.mpr hIn
      simp [hImage,hIn]
    · have hNoImage : hPosition k j k ∉ numericHTopPool k T := by
        intro h
        exact hIn (hSelected.mp h)
      simp [hNoImage,hIn]
  rw [← hqx, ← hwj]
  exact ⟨hForward.trans (hOriginal.trans hDec.symm),
    hReverse.trans (hOriginal.trans hDec.symm)⟩

#print axioms numericHTopPos_injective
#print axioms numericHTopPool_mem_iff
#print axioms numericHTopPool_mono
#print axioms reservedBlockNumericPrefix_disjoint_topPool
#print axioms finiteNumericH_reserved_prefix_top_support

end Kk
