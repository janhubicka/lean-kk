import Kk.LinkedAndFreshStage
import Kk.NumericHDesignatedPositive
import Kk.HensonZeroGenerationClique
import Mathlib.Tactic

/-!
# Genuine numerical-H old-original columns into a new TOP selected copy

English proof and 14-point hostile audit committed FIRST in
`docs/numeric_h_full_column_english_audit.md` before this Lean source.

The literal numerical-H generation gate is automatically open for ANY
older real generation q ≤ k into a new TOP-generation selected original:
q < k or q = k. The exact binary L bit (not merely a positive edge)
is therefore the original directed base relation bit.

For a symmetric Henson original graph, both tuple orientations agree and
every old-to-new reserved original NONEDGE stays absent between arbitrary
numerical generations, not just designated witness generations.

We compose these exact REAL numerical-H binary rules with the checked
actual Henson one-stage construction: complete old passing bits, fresh
clique positives, old/fresh all-generation nonedges, and unused gap zeros
hold in the SAME unmodified original graph and its true numerical H.

Only binary L atoms are certified here. The auxiliary E records,
full dependent (I1)--(I3)/(B3) upper L+ source closure, canonical
cover-age effect, and common labelled inverse source remain OPEN.
-/

namespace Kk

open SuccessorTree.V10

/-- EXACT directed binary L bit of the true numerical-H constructor
from ANY older real original at ANY generation q≤k to a strictly
later original at TOP generation k. The H gate is always open;
this statement covers both positive AND negative original atoms.
No symmetry or forbidden-family assumption is required. -/
theorem numericH_older_generation_to_top_exact
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q : Nat) (r : Fin d)
    (hij : i < j) (hq : q ≤ k) :
    hNumericBinary B k
      (hPosition k i q) (hPosition k j k) r = B i j r := by
  have hGate : q < k ∨ (q = k ∧ k = k) := by
    omega
  have hIff :
      hNumericBinary B k
          (hPosition k i q) (hPosition k j k) r = true ↔
        B i j r = true := by
    constructor
    · intro h
      exact ((hNumericBinary_real_forward_iff
        B k i j q k r hij hq le_rfl).1 h).2
    · intro h
      exact (hNumericBinary_real_forward_iff
        B k i j q k r hij hq le_rfl).2
          ⟨hGate, h⟩
  cases hb : B i j r with
  | false =>
      cases hh : hNumericBinary B k
        (hPosition k i q) (hPosition k j k) r with
      | false => rfl
      | true =>
          have hImpossible := hIff.mp hh
          simp [hb] at hImpossible
  | true =>
      simpa [hb] using (hIff.mpr hb)

/-- In a symmetric actual Henson original graph, the complete H
binary record from EVERY older real-generation copy to the next
top-generation selected copy agrees in BOTH directed orientations
with the corresponding ORIGINAL graph bits. -/
theorem numericH_henson_top_full_column_both
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (k i j q : Nat)
    (hij : i < j) (hq : q ≤ k) :
    (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k i q) (hPosition k j k) (0 : Fin 1) = E i j ∧
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k j k) (hPosition k i q) (0 : Fin 1) = E j i := by
  have hForward :
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k i q) (hPosition k j k) (0 : Fin 1) = E i j := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k i q) (hPosition k j k) (0 : Fin 1) = E i j
    exact numericH_older_generation_to_top_exact
      (normalizedGraphModel E).binary k i j q
      (0 : Fin 1) hij hq
  have hNormSym : ∀ x y t,
      (normalizedGraphModel E).binary x y t =
      (normalizedGraphModel E).binary y x t := by
    intro x y t
    fin_cases t
    change E x y = E y x
    exact hSym x y
  have hSwap :
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k i q) (hPosition k j k) (0 : Fin 1) =
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k j k) (hPosition k i q) (0 : Fin 1) := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k i q) (hPosition k j k) (0 : Fin 1) =
      hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k j k) (hPosition k i q) (0 : Fin 1)
    exact hNumericBinary_symmetric_of_base
      (normalizedGraphModel E).binary hNormSym k _ _
      (0 : Fin 1)
  refine ⟨hForward, ?_⟩
  exact hSwap.symm.trans (hForward.trans (hSym i j))

/-- Every ORIGINAL absent edge between an earlier original i
and a later original j remains absent in BOTH tuple orientations
among ALL real H generation copies q,m≤k. -/
theorem numericH_henson_nonedges_all_generations_both
    (E : Nat → Nat → Bool)
    (hSym : ∀ x y, E x y = E y x)
    (k i j q m : Nat)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (hE : E i j = false) :
    (infiniteNumericHL (normalizedGraphModel E) k).binary
      (hPosition k i q) (hPosition k j m) (0 : Fin 1) = false ∧
    (infiniteNumericHL (normalizedGraphModel E) k).binary
      (hPosition k j m) (hPosition k i q) (0 : Fin 1) = false := by
  have hMissing :
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k i q) (hPosition k j m) (0 : Fin 1) = false := by
    exact numericH_preserves_original_nonedge
      (normalizedGraphModel E) k i j q m hij hq hm
      (fun t => by
        fin_cases t
        change E i j = false
        exact hE) (0 : Fin 1)
  have hNormSym : ∀ x y t,
      (normalizedGraphModel E).binary x y t =
      (normalizedGraphModel E).binary y x t := by
    intro x y t
    fin_cases t
    change E x y = E y x
    exact hSym x y
  have hSwap :
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k i q) (hPosition k j m) (0 : Fin 1) =
      (infiniteNumericHL (normalizedGraphModel E) k).binary
        (hPosition k j m) (hPosition k i q) (0 : Fin 1) := by
    change hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k i q) (hPosition k j m) (0 : Fin 1) =
      hNumericBinary (normalizedGraphModel E).binary k
      (hPosition k j m) (hPosition k i q) (0 : Fin 1)
    exact hNumericBinary_symmetric_of_base
      (normalizedGraphModel E).binary hNormSym k _ _
      (0 : Fin 1)
  exact ⟨hMissing, hSwap.symm.trans hMissing⟩

/-- A PHYSICAL finite one-step gadget inside the UNCHANGED Henson
original graph and its literal numeric H L-reduct.

For any certified old selected passing column and any finite family
of freshly isolated reserved clique blocks of size <ell-1, the
numerical-H TOP selected copy has EXACTLY the prescribed adjacency
to EVERY older original at EVERY generation q≤ell, both ways.
Every old-to-new reserved nonedge is respected by ALL H generation
copies, and each fresh reserved clique has positive designated H
edges. All intervening original indices are accounted for.

This does NOT certify the intended graph-age COVER drop, the full
Kpt E-closure/corrected B3 continuation, or a canonical infinite
macrodiary/source-orbit induction. -/
theorem henson_leftDense_linked_fresh_stage_numericH_complete_L
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (base B : Nat)
    (block : Nat → Option (Fin B))
    (oldNeighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < base → y < base →
      block x = some b → block y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E base (ell-1)
      (fun x => if block x = none then oldNeighbour x else false) = false)
    (hBudget : ∀ b : Fin B,
      (liveReservedBlock base B block oldNeighbour b).card +
      finiteDirectedCliqueCapacity E
        (linkedUnreserved E base B block oldNeighbour b) < ell-1)
    (sizes : List Nat) (hSmall : ∀ r ∈ sizes, r < ell-1) :
    ∃ (fresh : List (Finset Nat)) (front v : Nat),
      fresh.map Finset.card = sizes ∧
      fresh.Pairwise (OrderedReservedBlockCrossNonedges E) ∧
      (∀ S ∈ fresh,
        (∀ x ∈ S, base ≤ x ∧ x < front) ∧
        IsDirectedCliqueOn E S ∧
        (∀ y ∈ S, ∀ x, x < y → x ∉ S →
          E x y = false ∧ E y x = false)) ∧
      front ≤ v ∧
      (∀ x : Nat, x < v → ∀ q : Nat, q ≤ ell →
        let bit : Bool :=
          if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion fresh))
          else false
        (infiniteNumericHL (normalizedGraphModel E) ell).binary
          (hPosition ell x q) (hPosition ell v ell)
          (0 : Fin 1) = bit ∧
        (infiniteNumericHL (normalizedGraphModel E) ell).binary
          (hPosition ell v ell) (hPosition ell x q)
          (0 : Fin 1) = bit) ∧
      (∀ S ∈ fresh, ∀ x : Nat, x < base → ∀ y ∈ S,
        ∀ q m : Nat, q ≤ ell → m ≤ ell →
          (infiniteNumericHL (normalizedGraphModel E) ell).binary
            (hPosition ell x q) (hPosition ell y m)
            (0 : Fin 1) = false ∧
          (infiniteNumericHL (normalizedGraphModel E) ell).binary
            (hPosition ell y m) (hPosition ell x q)
            (0 : Fin 1) = false) ∧
      (∀ S ∈ fresh, ∀ a b : Fin S.card, a < b →
        (infiniteNumericHL (normalizedGraphModel E) ell).binary
          (hPosition ell (S.orderEmbOfFin rfl a) a.val)
          (hPosition ell (S.orderEmbOfFin rfl b) b.val)
          (0 : Fin 1) = true) := by
  classical
  have hSym : ∀ i j, E i j = E j i :=
    hensonForbiddenFamily_symmetric ell hell E hAvoid
  obtain ⟨fresh, front, v, hCards, hPair, hProps,
      hOldFresh, hV, hColumn⟩ :=
    henson_leftDense_later_selected_after_fresh_blocks_of_link_capacity
      ell hell E hAvoid hDense base B block oldNeighbour
      hCross hPlain hBudget sizes hSmall
  refine ⟨fresh, front, v, hCards, hPair, hProps, hV,
    ?_, ?_, ?_⟩
  · intro x hx q hq
    have hNumeric :=
      numericH_henson_top_full_column_both E hSym ell x v q hx hq
    have hActual := hColumn x hx
    exact ⟨hNumeric.1.trans hActual.1,
      hNumeric.2.trans hActual.2⟩
  · intro S hS x hx y hy q m hq hm
    have hyBase : base ≤ y := ((hProps S hS).1 y hy).1
    have hxy : x < y := by omega
    exact numericH_henson_nonedges_all_generations_both
      E hSym ell x y q m hxy hq hm
      (hOldFresh S hS x hx y hy).1
  · intro S hS a b hab
    have hCardMem : S.card ∈ sizes := by
      rw [← hCards]
      exact List.mem_map.mpr ⟨S, hS, rfl⟩
    have hCardBound : S.card ≤ ell := by
      have hs := hSmall S.card hCardMem
      omega
    exact numericH_designated_clique_of_finite_set
      E ell S.card S rfl hCardBound (hProps S hS).2.1
      a b hab

end Kk
