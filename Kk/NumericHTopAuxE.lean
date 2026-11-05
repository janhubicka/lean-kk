import Kk.NumericHFullSelectedColumn
import SuccessorTree.V10.HExactE
import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Exact auxiliary E column of actual numerical-H TOP selected originals

The English proof and 14-point hostile audit were committed FIRST in
`docs/numeric_h_top_aux_e_english_audit.md` BEFORE this Lean source.

The true auxiliary E column at a top real target ι(j,k), j,k>0, is
an initial segment ending at the exact cut ι(j-1,k)+1, INCLUDING
every odd fake coordinate below that cut. Every earlier real original,
at every q≤k, has a POSITIVE incoming E incidence to that target,
even when the corresponding original binary L bit is zero.

At a genuine finite numerical-H target inside the carrier, this
is the exact finite E column and free level. Composing with the
verified physical L-bit theorem and a genuine Henson selected+fresh
one-stage construction gives the full old-original L records and
full incoming E/free-level column in ONE actual finite H+ prefix.

This is not the full E relation among arbitrary pairs or the
Kpt parameter-closed B3 source. E is directed: reverse E(selected,old)
is generally different, and source selection requires more than
a positive E bit. The K4 auxiliary-microevent counterexample remains.
-/

namespace Kk

open SuccessorTree.V10

/-- EXACT top-real auxiliary E-column in numerical H, for ALL lower
numerical coordinates u, including odd fake coordinates. The cut is
the first *missing* coordinate. No original graph L assumptions. -/
theorem numericH_top_auxE_true_iff
    (k j u : Nat) (hk : 0 < k) (hj : 0 < j) :
    exactHEBool k u (hPosition k j k) = true ↔
      u < hPosition k (j-1) k + 1 := by
  exact (exactHEBool_at_real_iff k j k u le_rfl).trans
    (generatedE_top_iff k j u hj hk)

/-- The ACTUAL finite numerical-H E table gives the identical top
column when its target real vertex belongs to the finite carrier.
In particular, no out-of-carrier E value is falsely asserted. -/
theorem finiteNumericH_top_auxE_true_iff
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N j u : Nat) (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < N) :
    (finiteNumericH K k N).E u (hPosition k j k) = true ↔
      u < hPosition k (j-1) k + 1 := by
  change finiteNumericHE k N u (hPosition k j k) = true ↔ _
  rw [finiteNumericHE_true_iff]
  exact (and_iff_right hTarget).trans
    (numericH_top_auxE_true_iff k j u hk hj)

/-- Every earlier genuine original at EVERY generation lies in
the auxiliary E initial segment of the new TOP selected copy,
irrespective of the old graph binary L adjacency bit. -/
theorem numericH_top_auxE_all_earlier_real
    (k i j q : Nat)
    (hk : 0 < k) (hj : 0 < j)
    (hij : i < j) (hq : q ≤ k) :
    exactHEBool k (hPosition k i q) (hPosition k j k) = true := by
  have hi : i ≤ j-1 := by omega
  have hPosLe : hPosition k i q ≤ hPosition k (j-1) k :=
    hPosition_mono k i (j-1) q k hi hq
  exact (numericH_top_auxE_true_iff
    k j (hPosition k i q) hk hj).2 (by omega)

/-- The canonical FREE LEVEL of a real top selected copy inside
the actual finite numerical-H+ constructor equals its literal
auxiliary E-column cutoff. This is NOT the target coordinate. -/
theorem finiteNumericH_top_freeLevel_exact
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N j : Nat) (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < N) :
    (finiteNumericH K k N).freeLevel (hPosition k j k) =
      hPosition k (j-1) k + 1 := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let target : Nat := hPosition k j k
  let cut : Nat := hPosition k (j-1) k + 1
  have hColumn : ∀ u, A.E u target = true ↔ u < cut := by
    intro u
    exact finiteNumericH_top_auxE_true_iff
      K k N j u hk hj hTarget
  have hCut : IsFreeCut A.E target cut := by
    constructor
    · intro u hu
      exact (hColumn u).2 hu
    · cases h : A.E cut target with
      | false => rfl
      | true =>
          have hc := (hColumn cut).1 h
          omega
  have hCanonical : IsFreeCut A.E target (A.freeLevel target) :=
    canonicalFreeLevel_isFreeCut A.E A.spaced A.downward target
  exact freeCut_unique A.E target (A.freeLevel target)
    cut hCanonical hCut

/-- Literal finite numerical-H+ L+ REALIZATION of one genuine
Henson selected successor after a family of fresh reserved cliques.

The selected top copy has the EXACT complete BINARY L column,
in both tuple orientations, against every previous real-generation
copy, including prior selected and old/new reserved originals,
all split/coding originals, and ALL skipped original indices.
The incoming auxiliary E-column at that same selected target is
the EXACT initial segment through ι(v-1,ell), so every earlier
real-generation copy is E-related to it, independently of L.
The canonical free level is proved from the actual finite E.

Old-to-fresh all-generation binary nonedges and designated
positive fresh clique atoms remain exact. The input old-column
mixed tests and Henson one-point left density remain explicit.
This does NOT assert a full physical canonical graph-age COVER
drop, identify Kpt source closure, decide corrected B3, or
construct a common labelled inverse source orbit. -/
theorem henson_leftDense_linked_fresh_stage_finiteNumericH_complete_LE
    (ell : Nat) (hell : 2 ≤ ell)
    (adj : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel adj))
    (hDense : OnePointLeftDense adj ell)
    (base B : Nat)
    (block : Nat → Option (Fin B))
    (oldNeighbour : Nat → Bool)
    (hCross : ∀ x y (b c : Fin B),
      x < base → y < base →
      block x = some b → block y = some c →
      b ≠ c → adj x y = false)
    (hPlain : finiteNeighbourCliqueCheck adj base (ell-1)
      (fun x => if block x = none then oldNeighbour x else false) = false)
    (hBudget : ∀ b : Fin B,
      (liveReservedBlock base B block oldNeighbour b).card +
      finiteDirectedCliqueCapacity adj
        (linkedUnreserved adj base B block oldNeighbour b) < ell-1)
    (sizes : List Nat) (hSmall : ∀ r ∈ sizes, r < ell-1)
    (hSomeFresh : ∃ r ∈ sizes, 0 < r) :
    ∃ (fresh : List (Finset Nat)) (front v N : Nat),
      fresh.map Finset.card = sizes ∧
      fresh.Pairwise (OrderedReservedBlockCrossNonedges adj) ∧
      (∀ S ∈ fresh,
        (∀ x ∈ S, base ≤ x ∧ x < front) ∧
        IsDirectedCliqueOn adj S ∧
        (∀ y ∈ S, ∀ x, x < y → x ∉ S →
          adj x y = false ∧ adj y x = false)) ∧
      front ≤ v ∧
      N = hPosition ell v ell + 1 ∧
      hPosition ell v ell < N ∧
      (∀ x : Nat, x < v → ∀ q : Nat, q ≤ ell →
        let bit : Bool :=
          if x < front then
            (if x < base then oldNeighbour x
             else decide (x ∈ reservedBlocksUnion fresh))
          else false
        (finiteNumericH (normalizedGraphModel adj) ell N).L.binary
          (hPosition ell x q) (hPosition ell v ell)
          (0 : Fin 1) = bit ∧
        (finiteNumericH (normalizedGraphModel adj) ell N).L.binary
          (hPosition ell v ell) (hPosition ell x q)
          (0 : Fin 1) = bit ∧
        (finiteNumericH (normalizedGraphModel adj) ell N).E
          (hPosition ell x q) (hPosition ell v ell) = true) ∧
      (∀ u : Nat,
        (finiteNumericH (normalizedGraphModel adj) ell N).E
          u (hPosition ell v ell) = true ↔
          u < hPosition ell (v-1) ell + 1) ∧
      (finiteNumericH (normalizedGraphModel adj) ell N).freeLevel
        (hPosition ell v ell) = hPosition ell (v-1) ell + 1 ∧
      (∀ S ∈ fresh, ∀ x : Nat, x < base → ∀ y ∈ S,
        ∀ q m : Nat, q ≤ ell → m ≤ ell →
          (finiteNumericH (normalizedGraphModel adj) ell N).L.binary
            (hPosition ell x q) (hPosition ell y m)
            (0 : Fin 1) = false ∧
          (finiteNumericH (normalizedGraphModel adj) ell N).L.binary
            (hPosition ell y m) (hPosition ell x q)
            (0 : Fin 1) = false) ∧
      (∀ S ∈ fresh, ∀ a b : Fin S.card, a < b →
        (finiteNumericH (normalizedGraphModel adj) ell N).L.binary
          (hPosition ell (S.orderEmbOfFin rfl a) a.val)
          (hPosition ell (S.orderEmbOfFin rfl b) b.val)
          (0 : Fin 1) = true) := by
  classical
  obtain ⟨fresh, front, v, hCards, hPair, hProps, hV, hL, hNon, hClique⟩ :=
    henson_leftDense_linked_fresh_stage_numericH_complete_L
      ell hell adj hAvoid hDense base B block oldNeighbour
      hCross hPlain hBudget sizes hSmall
  let N : Nat := hPosition ell v ell + 1
  have hvPos : 0 < v := by
    obtain ⟨r, hrSize, hrPos⟩ := hSomeFresh
    have hrInCards : r ∈ fresh.map Finset.card := by
      rw [hCards]
      exact hrSize
    obtain ⟨S, hS, hCard⟩ := List.mem_map.mp hrInCards
    have hSPos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hSPos
    have hxFront : x < front := ((hProps S hS).1 x hx).2
    omega
  have hHeight : 0 < ell := by omega
  have hTarget : hPosition ell v ell < N := by
    dsimp [N]
    omega
  have hFiniteE : ∀ u,
      (finiteNumericH (normalizedGraphModel adj) ell N).E
        u (hPosition ell v ell) = true ↔
        u < hPosition ell (v-1) ell + 1 := by
    intro u
    exact finiteNumericH_top_auxE_true_iff
      (normalizedGraphModel adj) ell N v u hHeight hvPos hTarget
  have hFreeLevel :
      (finiteNumericH (normalizedGraphModel adj) ell N).freeLevel
        (hPosition ell v ell) =
      hPosition ell (v-1) ell + 1 :=
    finiteNumericH_top_freeLevel_exact
      (normalizedGraphModel adj) ell N v hHeight hvPos hTarget
  refine ⟨fresh, front, v, N, hCards, hPair, hProps, hV, rfl,
    hTarget, ?_, hFiniteE, hFreeLevel, ?_, ?_⟩
  · intro x hx q hq
    have hLBits := hL x hx q hq
    have hEBit :
        (finiteNumericH (normalizedGraphModel adj) ell N).E
          (hPosition ell x q) (hPosition ell v ell) = true := by
      change finiteNumericHE ell N (hPosition ell x q)
        (hPosition ell v ell) = true
      apply (finiteNumericH_top_auxE_true_iff
        (normalizedGraphModel adj) ell N v
        (hPosition ell x q) hHeight hvPos hTarget).2
      have hxPre : x ≤ v-1 := by omega
      have hxPos :
          hPosition ell x q ≤ hPosition ell (v-1) ell :=
        hPosition_mono ell x (v-1) q ell hxPre hq
      omega
    exact ⟨hLBits.1, hLBits.2, hEBit⟩
  · intro S hS x hx y hy q m hq hm
    exact hNon S hS x hx y hy q m hq hm
  · intro S hS a b hab
    exact hClique S hS a b hab

end Kk
