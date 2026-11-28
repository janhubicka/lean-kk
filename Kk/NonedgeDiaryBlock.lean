import Kk.NonedgeProfileBridge
import Kk.IntegerAgeCoverRestriction
import Mathlib.Tactic

/-!
# Literal block descriptors for a two-vertex diary

These are finite algebraic transitions, not a new enumeration of
histories. The left/right labels are split labels, not coding order.
The retained graph reconstruction uses the unique essential changed
support and the forced clique size of a genuine age cover.
-/

namespace Kk.NonedgeHistory

inductive PairSupportKind where
  | left | right | joint
  deriving DecidableEq, Fintype

def PairSupportKind.valAt (t : PairSupportKind) (p : Bounds) : Nat :=
  match t with
  | .left => leftCapacity p
  | .right => rightCapacity p
  | .joint => jointCapacity p

def PairSupportKind.positive (t : PairSupportKind) : Bool × Bool :=
  match t with
  | .left => (true,false)
  | .right => (false,true)
  | .joint => (true,true)

def PairSupportKind.MinimalDrop (t : PairSupportKind) (q p : Bounds) : Prop :=
  t.valAt q < t.valAt p ∧
  (t = .joint → leftCapacity q = leftCapacity p ∧ rightCapacity q = rightCapacity p)

instance (t : PairSupportKind) (q p : Bounds) :
    Decidable (t.MinimalDrop q p) := by
  unfold PairSupportKind.MinimalDrop
  infer_instance

def essentialPairSupport (q p : Bounds) : PairSupportKind :=
  if leftCapacity q < leftCapacity p then .left
  else if rightCapacity q < rightCapacity p then .right else .joint

theorem essentialPairSupport_minimal_unique :
    ∀ q p : Bounds, Covers q p →
      (essentialPairSupport q p).MinimalDrop q p ∧
      ∀ t : PairSupportKind, t.MinimalDrop q p → t = essentialPairSupport q p := by
  decide

theorem essentialPairSupport_unit :
    ∀ q p : Bounds, Covers q p →
      (essentialPairSupport q p).valAt p = (essentialPairSupport q p).valAt q + 1 := by
  decide

def pairCoverBlockSize (q p : Bounds) : Nat :=
  3 - (essentialPairSupport q p).valAt q

theorem pairCoverBlockSize_bounds :
    ∀ q p : Bounds, Covers q p → 1 ≤ pairCoverBlockSize q p ∧ pairCoverBlockSize q p ≤ 2 := by
  decide

/-- The capacity-two clip imposed by one private marker on a single
occupied class is canonical and either neutral or a Hasse cover.
The third coordinate (joint capacity) does not change. -/
def markerPairClip (p : Bounds) (right : Bool) : Bounds :=
  if right then (p.1,min p.2.1 1,p.2.2)
  else (min p.1 1,p.2.1,p.2.2)

theorem markerPairClip_profile :
    ∀ p : Bounds, ∀ right : Bool, IsProfile p → IsProfile (markerPairClip p right) := by
  decide

theorem markerPairClip_cover_or_eq :
    ∀ p : Bounds, ∀ right : Bool, IsProfile p →
      markerPairClip p right = p ∨ Covers (markerPairClip p right) p := by
  decide

theorem rank_capacity_clip_two :
    ∀ r : Rank, capacity (min r 1) = min (capacity r) 2 := by
  decide

/-- All natural-valued clique multiplicities, not a sampled list of
small profiles, satisfy the exact marker clipping formula. -/
theorem markerPairClip_feasible (p : Bounds) (right : Bool) (x y : Nat) :
    Feasible (markerPairClip p right) x y ↔
      Feasible p x y ∧ (if right then y ≤ 2 else x ≤ 2) := by
  cases right <;>
    simp [markerPairClip, Feasible, leftCapacity, rightCapacity, jointCapacity,
      rank_capacity_clip_two, le_min_iff] <;> omega

theorem markerUnaryClip_cover_or_eq :
    ∀ r : Rank, min r 1 = r ∨ capacity (min r 1) + 1 = capacity r := by
  decide

end Kk.NonedgeHistory
