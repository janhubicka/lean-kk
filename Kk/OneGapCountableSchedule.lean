import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Chronological enumeration of finite batches

English proof and application boundaries:
`docs/one_gap_countable_schedule_english_audit_20261126.md`.

Construct the tagged enumeration from positive finite batch sizes. Each
batch occupies exactly one interval, and earlier batches occupy exactly
the corresponding initial segment. Reading actual pairwise disjoint,
nonrepeating lists then gives an injective enumeration of their union.
Extracting those lists from a resolved countable construction is separate.
-/

namespace Kk

def oneGapBatchBoundary (size : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => oneGapBatchBoundary size n + size n

@[simp] theorem oneGapBatchBoundary_zero (size : Nat → Nat) :
    oneGapBatchBoundary size 0 = 0 := rfl

@[simp] theorem oneGapBatchBoundary_succ (size : Nat → Nat) (n : Nat) :
    oneGapBatchBoundary size (n+1) = oneGapBatchBoundary size n + size n := rfl

theorem oneGapBatchBoundary_strictMono (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) : StrictMono (oneGapBatchBoundary size) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [oneGapBatchBoundary_succ]
  exact Nat.lt_add_of_pos_right (hPositive n)

theorem oneGapBatchBoundary_ge (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (n : Nat) :
    n ≤ oneGapBatchBoundary size n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := hPositive n
      rw [oneGapBatchBoundary_succ]
      omega

theorem oneGapBatchBoundary_covers (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k : Nat) :
    ∃ n, k < oneGapBatchBoundary size (n+1) :=
  ⟨k,lt_of_lt_of_le (Nat.lt_succ_self k)
    (oneGapBatchBoundary_ge size hPositive (k+1))⟩

/-- The first batch whose ending boundary lies after the given position. -/
def oneGapBatchIndex (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k : Nat) : Nat :=
  Nat.find (oneGapBatchBoundary_covers size hPositive k)

theorem oneGapBatchIndex_bounds (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k : Nat) :
    oneGapBatchBoundary size (oneGapBatchIndex size hPositive k) ≤ k ∧
      k < oneGapBatchBoundary size (oneGapBatchIndex size hPositive k + 1) := by
  refine ⟨?_,Nat.find_spec (oneGapBatchBoundary_covers size hPositive k)⟩
  by_cases hZero : oneGapBatchIndex size hPositive k = 0
  · simp [hZero]
  · have hMin := Nat.find_min (oneGapBatchBoundary_covers size hPositive k)
      (m := oneGapBatchIndex size hPositive k - 1)
      (by change _ < oneGapBatchIndex size hPositive k; omega)
    have hPred : oneGapBatchIndex size hPositive k - 1 + 1 =
        oneGapBatchIndex size hPositive k := by omega
    rw [hPred] at hMin
    exact Nat.le_of_not_gt hMin

theorem oneGapBatchIndex_eq_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k n : Nat) :
    oneGapBatchIndex size hPositive k = n ↔
      oneGapBatchBoundary size n ≤ k ∧ k < oneGapBatchBoundary size (n+1) := by
  constructor
  · intro h
    simpa only [h] using oneGapBatchIndex_bounds size hPositive k
  · rintro ⟨hLower,hUpper⟩
    apply (Nat.find_eq_iff (oneGapBatchBoundary_covers size hPositive k)).mpr
    refine ⟨hUpper,?_⟩
    intro m hmn hBad
    have hLe := (oneGapBatchBoundary_strictMono size hPositive).monotone
      (show m+1 ≤ n by omega)
    omega

def oneGapBatchPosition (size : Nat → Nat) (x : (n : Nat) × Fin (size n)) : Nat :=
  oneGapBatchBoundary size x.1 + x.2.val

/-- A genuine tagged entry for every natural position, with no
assumption about vertex names or disjointness between batches. -/
def oneGapBatchLocation (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k : Nat) : (n : Nat) × Fin (size n) :=
  ⟨oneGapBatchIndex size hPositive k,
    ⟨k - oneGapBatchBoundary size (oneGapBatchIndex size hPositive k),by
      have h := oneGapBatchIndex_bounds size hPositive k
      rw [oneGapBatchBoundary_succ] at h
      omega⟩⟩

theorem oneGapBatchPosition_location (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k : Nat) :
    oneGapBatchPosition size (oneGapBatchLocation size hPositive k) = k := by
  have h := (oneGapBatchIndex_bounds size hPositive k).1
  change oneGapBatchBoundary size (oneGapBatchIndex size hPositive k) +
    (k - oneGapBatchBoundary size (oneGapBatchIndex size hPositive k)) = k
  omega

theorem oneGapBatchPosition_bounds (size : Nat → Nat)
    (x : (n : Nat) × Fin (size n)) :
    oneGapBatchBoundary size x.1 ≤ oneGapBatchPosition size x ∧
      oneGapBatchPosition size x < oneGapBatchBoundary size (x.1+1) := by
  have h := x.2.isLt
  simp only [oneGapBatchPosition,oneGapBatchBoundary_succ]
  omega

theorem oneGapBatchPosition_injective (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) : Function.Injective (oneGapBatchPosition size) := by
  rintro ⟨n,i⟩ ⟨m,j⟩ hEq
  have hn := oneGapBatchPosition_bounds size ⟨n,i⟩
  have hm := oneGapBatchPosition_bounds size ⟨m,j⟩
  have hN := (oneGapBatchIndex_eq_iff size hPositive _ n).mpr hn
  have hM := (oneGapBatchIndex_eq_iff size hPositive _ m).mpr hm
  rw [hEq] at hN
  have he : n = m := hN.symm.trans hM
  subst m
  have hi : i = j := by
    apply Fin.ext
    change oneGapBatchBoundary size n + i.val =
      oneGapBatchBoundary size n + j.val at hEq
    omega
  subst j
  rfl

theorem oneGapBatchLocation_position (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (x : (n : Nat) × Fin (size n)) :
    oneGapBatchLocation size hPositive (oneGapBatchPosition size x) = x := by
  apply oneGapBatchPosition_injective size hPositive
  exact oneGapBatchPosition_location size hPositive _

def oneGapBatchEquiv (size : Nat → Nat) (hPositive : ∀ n, 0 < size n) :
    ((n : Nat) × Fin (size n)) ≃ Nat where
  toFun := oneGapBatchPosition size
  invFun := oneGapBatchLocation size hPositive
  left_inv := oneGapBatchLocation_position size hPositive
  right_inv := oneGapBatchPosition_location size hPositive

/-- A complete batch occupies precisely its prescribed interval. -/
theorem oneGapBatchLocation_batch_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k n : Nat) :
    (oneGapBatchLocation size hPositive k).1 = n ↔
      oneGapBatchBoundary size n ≤ k ∧ k < oneGapBatchBoundary size (n+1) :=
  oneGapBatchIndex_eq_iff size hPositive k n

/-- Whole-batch retention cannot straddle an omitted coordinate of
a different batch. This concerns chronological positions. -/
theorem oneGapBatchLocation_convex (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (a b c n : Nat)
    (hab : a ≤ b) (hbc : b ≤ c)
    (ha : (oneGapBatchLocation size hPositive a).1 = n)
    (hc : (oneGapBatchLocation size hPositive c).1 = n) :
    (oneGapBatchLocation size hPositive b).1 = n := by
  apply (oneGapBatchLocation_batch_iff size hPositive b n).mpr
  have hA := (oneGapBatchLocation_batch_iff size hPositive a n).mp ha
  have hC := (oneGapBatchLocation_batch_iff size hPositive c n).mp hc
  omega

theorem oneGapBatchLocation_before_boundary (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (k n : Nat) :
    (oneGapBatchLocation size hPositive k).1 < n ↔
      k < oneGapBatchBoundary size n := by
  have h := oneGapBatchIndex_bounds size hPositive k
  have hMono := (oneGapBatchBoundary_strictMono size hPositive).monotone
  change oneGapBatchIndex size hPositive k < n ↔ _
  constructor
  · intro hLt
    have hLe := hMono (show oneGapBatchIndex size hPositive k + 1 ≤ n by omega)
    omega
  · intro hk
    by_contra hNot
    have hLe := hMono (show n ≤ oneGapBatchIndex size hPositive k by omega)
    omega

def oneGapBatchValue {α : Type*} (batch : Nat → List α)
    (x : (n : Nat) × Fin (batch n).length) : α :=
  (batch x.1).get x.2

def oneGapChronologicalVertex {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length) (k : Nat) : α :=
  oneGapBatchValue batch
    (oneGapBatchLocation (fun n => (batch n).length) hPositive k)

theorem oneGapChronologicalVertex_at_position {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length) (n : Nat) (i : Fin (batch n).length) :
    oneGapChronologicalVertex batch hPositive
      (oneGapBatchPosition (fun n => (batch n).length) ⟨n,i⟩) = (batch n)[i.val] := by
  exact congrArg (oneGapBatchValue batch)
    (oneGapBatchLocation_position (fun n => (batch n).length) hPositive ⟨n,i⟩)

theorem oneGapChronologicalVertex_mem {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length) (k : Nat) :
    oneGapChronologicalVertex batch hPositive k ∈
      batch (oneGapBatchLocation (fun n => (batch n).length) hPositive k).1 :=
  List.getElem_mem _

theorem oneGapChronologicalVertex_range {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length) (v : α) :
    (∃ k, oneGapChronologicalVertex batch hPositive k = v) ↔
      ∃ n, v ∈ batch n := by
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨_,oneGapChronologicalVertex_mem batch hPositive k⟩
  · rintro ⟨n,hv⟩
    obtain ⟨i,hi,hEq⟩ := List.mem_iff_getElem.mp hv
    refine ⟨oneGapBatchPosition (fun n => (batch n).length) ⟨n,⟨i,hi⟩⟩,?_⟩
    rw [oneGapChronologicalVertex_at_position]
    exact hEq

/-- The precise vertex set at a batch boundary, not only a cardinal
bound or an inclusion in the countable union. -/
theorem oneGapChronologicalVertex_prefix {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length) (v : α) (n : Nat) :
    (∃ k, k < oneGapBatchBoundary (fun n => (batch n).length) n ∧
      oneGapChronologicalVertex batch hPositive k = v) ↔
      ∃ m, m < n ∧ v ∈ batch m := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨_,(oneGapBatchLocation_before_boundary _ hPositive k n).mpr hk,
      oneGapChronologicalVertex_mem batch hPositive k⟩
  · rintro ⟨m,hm,hv⟩
    obtain ⟨i,hi,hEq⟩ := List.mem_iff_getElem.mp hv
    let x : (m : Nat) × Fin (batch m).length := ⟨m,⟨i,hi⟩⟩
    refine ⟨oneGapBatchPosition (fun n => (batch n).length) x,?_,?_⟩
    · apply (oneGapBatchLocation_before_boundary _ hPositive _ n).mp
      rw [oneGapBatchLocation_position]
      exact hm
    · exact (oneGapChronologicalVertex_at_position batch hPositive m ⟨i,hi⟩).trans hEq

theorem oneGapChronologicalVertex_injective {α : Type*} (batch : Nat → List α)
    (hPositive : ∀ n, 0 < (batch n).length)
    (hNodup : ∀ n, (batch n).Nodup)
    (hDisjoint : ∀ n m, n ≠ m → List.Disjoint (batch n) (batch m)) :
    Function.Injective (oneGapChronologicalVertex batch hPositive) := by
  intro a b hEq
  let x := oneGapBatchLocation (fun n => (batch n).length) hPositive a
  let y := oneGapBatchLocation (fun n => (batch n).length) hPositive b
  have hx : (batch x.1).get x.2 ∈ batch x.1 := List.get_mem ..
  have hy : (batch y.1).get y.2 ∈ batch y.1 := List.get_mem ..
  change (batch x.1).get x.2 = (batch y.1).get y.2 at hEq
  have hBatch : x.1 = y.1 := by
    by_contra hNe
    exact hDisjoint x.1 y.1 hNe hx (hEq.symm ▸ hy)
  have hTag : x = y := by
    obtain ⟨n,i⟩ := x
    obtain ⟨m,j⟩ := y
    dsimp only at hBatch hEq
    subst m
    have hij : i = j := (hNodup n).injective_get hEq
    subst j
    rfl
  have hPos := congrArg (oneGapBatchPosition (fun n => (batch n).length)) hTag
  exact (oneGapBatchPosition_location _ hPositive a).symm.trans
    (hPos.trans (oneGapBatchPosition_location _ hPositive b))

end Kk
