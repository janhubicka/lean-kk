import Kk.LinkedCliqueCapacityUpdate
import Mathlib.Tactic

/-!
# Exact four-quadrant update when the LIVE RESERVED SET changes

The English proof and hostile 11-point audit were committed FIRST in
`docs/live_pool_four_quadrants_english_audit.md`, before this Lean module.

The actual next linked-unreserved originals can change for TWO independent
reasons: (i) a different set of unreserved originals is a positive neighbour
of the next proposed selected vertex; and (ii) a different set of reserved
vertices within the block is positive. Each set can GAIN and LOSE members.

The linked set for the next column is computed EXACTLY as four directed-edge
interaction sets: kept-unreserved/kept-reserved,
kept-unreserved/activated-reserved, newly-unreserved/kept-reserved, and
newly-unreserved/activated-reserved. This avoids silently keeping stale links
through DEACTIVATED reserved vertices. It also includes newly positive gap
originals.

The specialized theorem permits a different old and next original prefix,
a different old/next reserved-block tag type, and an explicit OPTIONAL old
block correspondence for each new block. No equality of the actual source
assigned I1/I2/I3/B3 types or Kpt monoid envelopes is inferred.

The resulting sufficient next-stage negative COMPLETE neighbourhood test
is an actual finite original-graph theorem, still CONDITIONAL on next-stage
cross-block nonedges, the pure-unreserved checker, and the updated budgets.
-/

namespace Kk

/-- Actual directed links FROM unreserved positive candidates U
TO live reserved witnesses R. This is deliberately not the MUTUAL
compatibility relation for directed cliques in PR #58. -/
def linkedOriginalsTo
    (E : Nat → Nat → Bool) (U R : Finset Nat) : Finset Nat :=
  U.filter (fun x => ∃ y ∈ R, E x y = true)

/-- Changing the unreserved positive candidates distributes exactly. -/
theorem linkedOriginalsTo_union_candidates
    (E : Nat → Nat → Bool) (U G R : Finset Nat) :
    linkedOriginalsTo E (U ∪ G) R =
      linkedOriginalsTo E U R ∪ linkedOriginalsTo E G R := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hIn, hLink⟩ := Finset.mem_filter.mp hx
    rcases Finset.mem_union.mp hIn with hU | hG
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hU, hLink⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hG, hLink⟩))
  · intro hx
    rcases Finset.mem_union.mp hx with hxU | hxG
    · obtain ⟨hU, hLink⟩ := Finset.mem_filter.mp hxU
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union.mpr (Or.inl hU), hLink⟩
    · obtain ⟨hG, hLink⟩ := Finset.mem_filter.mp hxG
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union.mpr (Or.inr hG), hLink⟩

/-- Activation of additional live reserved witnesses distributes
exactly. This checks the ACTUAL directed edge x → y. -/
theorem linkedOriginalsTo_union_reserved
    (E : Nat → Nat → Bool) (U R A : Finset Nat) :
    linkedOriginalsTo E U (R ∪ A) =
      linkedOriginalsTo E U R ∪ linkedOriginalsTo E U A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxU, y, hyRA, hEdge⟩ := Finset.mem_filter.mp hx
    rcases Finset.mem_union.mp hyRA with hyR | hyA
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hxU, y, hyR, hEdge⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hxU, y, hyA, hEdge⟩))
  · intro hx
    rcases Finset.mem_union.mp hx with hxR | hxA
    · obtain ⟨hxU, y, hyR, hEdge⟩ := Finset.mem_filter.mp hxR
      exact Finset.mem_filter.mpr
        ⟨hxU, y, Finset.mem_union.mpr (Or.inl hyR), hEdge⟩
    · obtain ⟨hxU, y, hyA, hEdge⟩ := Finset.mem_filter.mp hxA
      exact Finset.mem_filter.mpr
        ⟨hxU, y, Finset.mem_union.mpr (Or.inr hyA), hEdge⟩

/-- Explicit four-way update: both positive-unreserved and live-reserved
sets may grow OR shrink. Stale links through deactivated witnesses disappear. -/
def updatedLinkedOriginals
    (E : Nat → Nat → Bool)
    (U0 U1 R0 R1 : Finset Nat) : Finset Nat :=
  (linkedOriginalsTo E (U0 ∩ U1) (R0 ∩ R1) ∪
    linkedOriginalsTo E (U0 ∩ U1) (R1 \ R0)) ∪
  (linkedOriginalsTo E (U1 \ U0) (R0 ∩ R1) ∪
    linkedOriginalsTo E (U1 \ U0) (R1 \ R0))

/-- All four interaction quadrants are NECESSARY for an exact update:
kept U and kept R; kept U with activated R; new U with kept R;
and new U with activated R. This formula is true for directed graphs. -/
theorem linkedOriginalsTo_four_quadrants
    (E : Nat → Nat → Bool) (U0 U1 R0 R1 : Finset Nat) :
    linkedOriginalsTo E U1 R1 =
      updatedLinkedOriginals E U0 U1 R0 R1 := by
  classical
  have hU : (U0 ∩ U1) ∪ (U1 \ U0) = U1 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hR : (R0 ∩ R1) ∪ (R1 \ R0) = R1 := by
    ext y
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  unfold updatedLinkedOriginals
  calc
    linkedOriginalsTo E U1 R1 =
      linkedOriginalsTo E ((U0 ∩ U1) ∪ (U1 \ U0))
        ((R0 ∩ R1) ∪ (R1 \ R0)) := by rw [hU, hR]
    _ = _ := by
      rw [linkedOriginalsTo_union_candidates]
      rw [linkedOriginalsTo_union_reserved, linkedOriginalsTo_union_reserved]

/-- An unmatched newly created reserved block has NO prior live
original witness. A matched one uses the actual prior original indices.
The optional label map is an explicit comparison INPUT, not an
unproved canonical diary source identification. -/
def previousLiveReserved
    (N0 B0 B1 : Nat) (oldBlock : Nat → Option (Fin B0))
    (oldNeighbour : Nat → Bool)
    (previousLabel : Fin B1 → Option (Fin B0))
    (b : Fin B1) : Finset Nat :=
  match previousLabel b with
  | none => ∅
  | some a => liveReservedBlock N0 B0 oldBlock oldNeighbour a

/-- The exact four-quadrant update for ACTUAL old and new prefix,
tags and passing columns. The old and next tag spaces may differ.
Both older selected/parameter originals and newly positive gap originals
are included through the actual liveUnreserved sets. -/
def updatedActualLinkedPool
    (E : Nat → Nat → Bool) (N0 B0 N1 B1 : Nat)
    (oldBlock : Nat → Option (Fin B0))
    (newBlock : Nat → Option (Fin B1))
    (oldNeighbour newNeighbour : Nat → Bool)
    (previousLabel : Fin B1 → Option (Fin B0))
    (b : Fin B1) : Finset Nat :=
  updatedLinkedOriginals E
    (liveUnreserved N0 B0 oldBlock oldNeighbour)
    (liveUnreserved N1 B1 newBlock newNeighbour)
    (previousLiveReserved N0 B0 B1 oldBlock oldNeighbour previousLabel b)
    (liveReservedBlock N1 B1 newBlock newNeighbour b)

/-- Exact identification, no assumed stagewise subset monotonicity:
deactivated old reserved witnesses and no-longer-positive unreserved
originals are NOT carried into the next linked pool. -/
theorem linkedUnreserved_eq_updatedActualLinkedPool
    (E : Nat → Nat → Bool) (N0 B0 N1 B1 : Nat)
    (oldBlock : Nat → Option (Fin B0))
    (newBlock : Nat → Option (Fin B1))
    (oldNeighbour newNeighbour : Nat → Bool)
    (previousLabel : Fin B1 → Option (Fin B0))
    (b : Fin B1) :
    linkedUnreserved E N1 B1 newBlock newNeighbour b =
      updatedActualLinkedPool E N0 B0 N1 B1
        oldBlock newBlock oldNeighbour newNeighbour previousLabel b := by
  exact linkedOriginalsTo_four_quadrants E
    (liveUnreserved N0 B0 oldBlock oldNeighbour)
    (liveUnreserved N1 B1 newBlock newNeighbour)
    (previousLiveReserved N0 B0 B1 oldBlock oldNeighbour previousLabel b)
    (liveReservedBlock N1 B1 newBlock newNeighbour b)

/-- A complete new-neighbourhood certificate from the EXACT changed
live-reserved/unreserved interaction records, retaining every new
split/coding parameter and genuine enumeration gap bit.
This is a SUFFICIENT capacity check, not an automatic diary invariant. -/
theorem finiteNeighbourCliqueCheck_false_of_updatedActualLinkedPool_budget
    (E : Nat → Nat → Bool)
    (N0 B0 N1 B1 q : Nat)
    (oldBlock : Nat → Option (Fin B0))
    (newBlock : Nat → Option (Fin B1))
    (oldNeighbour newNeighbour : Nat → Bool)
    (previousLabel : Fin B1 → Option (Fin B0))
    (hCross : ∀ x y (b c : Fin B1),
      x < N1 → y < N1 →
      newBlock x = some b → newBlock y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E N1 q
      (fun x => if newBlock x = none then newNeighbour x else false) = false)
    (hBudget : ∀ b : Fin B1,
      (liveReservedBlock N1 B1 newBlock newNeighbour b).card +
        finiteDirectedCliqueCapacity E
          (updatedActualLinkedPool E N0 B0 N1 B1
            oldBlock newBlock oldNeighbour newNeighbour previousLabel b) < q) :
    finiteNeighbourCliqueCheck E N1 q newNeighbour = false := by
  apply finiteNeighbourCliqueCheck_false_of_link_capacity
    E N1 q B1 newBlock newNeighbour hCross hPlain
  intro b
  rw [linkedUnreserved_eq_updatedActualLinkedPool E N0 B0 N1 B1
    oldBlock newBlock oldNeighbour newNeighbour previousLabel b]
  exact hBudget b

/-- Under the independent chosen Henson left-density property, the
updated genuine-original next passing column is realized after the
complete finite old-neighbourhood certificate has been established. -/
theorem henson_leftDense_realizes_of_updatedActualLinkedPool_budget
    (ell : Nat) (hell : 2 ≤ ell)
    (E : Nat → Nat → Bool)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (hDense : OnePointLeftDense E ell)
    (N0 B0 N1 B1 : Nat)
    (oldBlock : Nat → Option (Fin B0))
    (newBlock : Nat → Option (Fin B1))
    (oldNeighbour newNeighbour : Nat → Bool)
    (previousLabel : Fin B1 → Option (Fin B0))
    (hCross : ∀ x y (b c : Fin B1),
      x < N1 → y < N1 →
      newBlock x = some b → newBlock y = some c →
      b ≠ c → E x y = false)
    (hPlain : finiteNeighbourCliqueCheck E N1 (ell-1)
      (fun x => if newBlock x = none then newNeighbour x else false) = false)
    (hBudget : ∀ b : Fin B1,
      (liveReservedBlock N1 B1 newBlock newNeighbour b).card +
        finiteDirectedCliqueCapacity E
          (updatedActualLinkedPool E N0 B0 N1 B1
            oldBlock newBlock oldNeighbour newNeighbour previousLabel b) < ell-1) :
    ∃ v : Nat, N1 ≤ v ∧
      ∀ x, x < v →
        E x v = (if x < N1 then newNeighbour x else false) ∧
        E v x = (if x < N1 then newNeighbour x else false) := by
  have hCheck :=
    finiteNeighbourCliqueCheck_false_of_updatedActualLinkedPool_budget
      E N0 B0 N1 B1 (ell-1) oldBlock newBlock oldNeighbour
      newNeighbour previousLabel hCross hPlain hBudget
  exact henson_leftDense_realizes_certified_original
    ell hell E hAvoid hDense N1 newNeighbour hCheck

/-- A directed counter-regression: old R={0}, next R={1}; unreserved
positive 2 has E(2,0)=true but E(2,1)=false. Old linked vertex 2
MUST disappear. A naive monotone-union update is false. -/
def staleReservedLinkEdge (i j : Nat) : Bool :=
  decide (i = 2 ∧ j = 0)

theorem stale_reserved_link_disappears :
    linkedOriginalsTo staleReservedLinkEdge ({2} : Finset Nat) {0} = {2} ∧
    linkedOriginalsTo staleReservedLinkEdge ({2} : Finset Nat) {1} = ∅ ∧
    updatedLinkedOriginals staleReservedLinkEdge
      ({2} : Finset Nat) {2} {0} {1} = ∅ := by
  decide

/-- An actual directed activation example: kept unreserved 2 links
only to NEW reserved 1, and NEW unreserved 3 links only to retained
reserved 0. BOTH distinct change quadrants are necessary. -/
def activatedReservedAndGapEdge (i j : Nat) : Bool :=
  decide ((i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 0))

theorem activated_reserve_and_gap_links :
    linkedOriginalsTo activatedReservedAndGapEdge
      ({2} : Finset Nat) {0} = ∅ ∧
    linkedOriginalsTo activatedReservedAndGapEdge
      ({2,3} : Finset Nat) {0,1} = {2,3} ∧
    updatedLinkedOriginals activatedReservedAndGapEdge
      ({2} : Finset Nat) {2,3} {0} {0,1} = {2,3} := by
  decide

end Kk
