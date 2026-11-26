import Kk.OneGapPartialStructure
import SuccessorTree.V10.GPlusRetainedCoordinates
import Mathlib.Tactic

/-!
# Exact finite one-gap compression

Keep the anchor and a complete gap/ordinary pair at each selected index.
The entire auxiliary table is recovered from order and pair adjacency;
it is not an additional equality hypothesis on two occurrences.

English proof and boundaries: `docs/one_gap_compression_english_audit_20261126.md`.
-/

namespace Kk
open SuccessorTree.V10

/-- Lift a selection of ordinary indices to their complete retained pairs. -/
def oneGapLift (f : Nat → Nat) (v : Nat) : Nat :=
  if v = 0 then 0 else 2 * f ((v - 1) / 2) + 1 + (v - 1) % 2

@[simp] theorem oneGapLift_zero (f : Nat → Nat) : oneGapLift f 0 = 0 := by
  simp [oneGapLift]

@[simp] theorem oneGapLift_gap (f : Nat → Nat) (i : Nat) :
    oneGapLift f (2 * i + 1) = 2 * f i + 1 := by
  simp [oneGapLift]

@[simp] theorem oneGapLift_address (f : Nat → Nat) (i : Nat) :
    oneGapLift f (oneGapAddress i) = oneGapAddress (f i) := by
  have hn : oneGapAddress i ≠ 0 := by unfold oneGapAddress; omega
  have h : (oneGapAddress i - 1) / 2 = i := by unfold oneGapAddress; omega
  have hm : (oneGapAddress i - 1) % 2 = 1 := by unfold oneGapAddress; omega
  simp only [oneGapLift, ite_eq_right hn, h, hm]
  unfold oneGapAddress
  omega

theorem oneGapLift_strictMono (f : Nat → Nat) (hf : StrictMono f) :
    StrictMono (oneGapLift f) := by
  intro u v huv
  by_cases hu : u = 0
  · subst u
    have hv : v ≠ 0 := by omega
    change 0 < oneGapLift f v
    simp only [oneGapLift, ite_eq_right hv]
    omega
  · have hv : v ≠ 0 := by omega
    simp only [oneGapLift, ite_eq_right hu, ite_eq_right hv]
    by_cases hq : (u-1)/2 = (v-1)/2
    · rw [hq]
      omega
    · have hlt : (u-1)/2 < (v-1)/2 := by omega
      have hfl := hf hlt
      omega

@[simp] theorem oneGapLift_real_iff (f : Nat → Nat) (v : Nat) :
    oneGapReal (oneGapLift f v) ↔ oneGapReal v := by
  by_cases hv : v = 0
  · subst v
    simp [oneGapReal]
  · unfold oneGapReal oneGapLift
    rw [ite_eq_right hv]
    omega

theorem oneGapLift_preceding_gap (f : Nat → Nat) (v : Nat)
    (hv : oneGapReal v) :
    oneGapLift f (v-1) + 1 = oneGapLift f v := by
  rw [← oneGapAddress_index hv]
  have hGap : oneGapAddress (oneGapIndex v) - 1 = 2 * oneGapIndex v + 1 := by
    unfold oneGapAddress
    omega
  rw [hGap, oneGapLift_gap, oneGapLift_address]
  unfold oneGapAddress
  omega

/-- All ordinary entries, including nonedges and diagonal binary entries. -/
theorem oneGapLift_edge (G : Nat → Nat → Bool) (f : Nat → Nat) (u v : Nat) :
    oneGapEdge G (oneGapLift f u) (oneGapLift f v) =
      oneGapEdge (fun i j => G (f i) (f j)) u v := by
  by_cases hu : oneGapReal u
  · by_cases hv : oneGapReal v
    · rw [← oneGapAddress_index hu, ← oneGapAddress_index hv]
      simp only [oneGapLift_address, oneGapEdge_address]
    · simp [oneGapEdge, hv]
  · simp [oneGapEdge, hu]

/-- Complete auxiliary-table identity, including reversed pairs and loops. -/
theorem oneGapLift_aux (f : Nat → Nat) (hf : StrictMono f) (u v : Nat) :
    oneGapAux (oneGapLift f u) (oneGapLift f v) = oneGapAux u v := by
  by_cases hv : oneGapReal v
  · have hGap := oneGapLift_preceding_gap f v hv
    have hMono := oneGapLift_strictMono f hf
    have hSpace : oneGapLift f u + 1 < oneGapLift f v ↔ u + 1 < v := by
      rw [← hGap]
      constructor
      · intro h
        have hlt : oneGapLift f u < oneGapLift f (v-1) := by omega
        have hOrig : u < v-1 := (hMono.lt_iff_lt).mp hlt
        omega
      · intro h
        have hOrig : u < v-1 := by omega
        have hlt := hMono hOrig
        omega
    simp only [oneGapAux, oneGapLift_real_iff, hv, true_and]
    simp only [hSpace]
  · simp [oneGapAux, hv]

/-- The actual retained full table on the anchor and the first `n` pairs. -/
def oneGapRetainedCode (G : Nat → Nat → Bool) (f : Nat → Nat) (n : Nat) :
    FinitePartialCode 1 0 1 where
  size := 2*n+1
  binary := fun i j _ => oneGapEdge G (oneGapLift f i.val) (oneGapLift f j.val)
  unary := fun _ t => Fin.elim0 t
  diagonal := fun i _ => oneGapEdge G (oneGapLift f i.val) (oneGapLift f i.val)
  eRelation := fun i j => oneGapAux (oneGapLift f i.val) (oneGapLift f j.val)

/-- Compression is literally the ordinary induced graph with one-gap padding. -/
theorem oneGapRetainedCode_eq_prefix
    (G : Nat → Nat → Bool) (f : Nat → Nat) (hf : StrictMono f) (n : Nat) :
    oneGapRetainedCode G f n =
      (oneGapPartial (fun i j => G (f i) (f j))).prefixCode (2*n+1) := by
  have hBin : (fun i j : Fin (2*n+1) => fun _ : Fin 1 =>
      oneGapEdge G (oneGapLift f i.val) (oneGapLift f j.val)) =
      (fun i j : Fin (2*n+1) => fun _ : Fin 1 =>
        oneGapEdge (fun a b => G (f a) (f b)) i.val j.val) := by
    funext i j t
    exact oneGapLift_edge G f i.val j.val
  have hE : (fun i j : Fin (2*n+1) =>
      oneGapAux (oneGapLift f i.val) (oneGapLift f j.val)) =
      (fun i j : Fin (2*n+1) => oneGapAux i.val j.val) := by
    funext i j
    exact oneGapLift_aux f hf i.val j.val
  have hD : (fun i : Fin (2*n+1) => fun _ : Fin 1 =>
      oneGapEdge G (oneGapLift f i.val) (oneGapLift f i.val)) =
      (fun i : Fin (2*n+1) => fun _ : Fin 1 =>
        oneGapEdge (fun a b => G (f a) (f b)) i.val i.val) := by
    funext i t
    exact oneGapLift_edge G f i.val i.val
  unfold oneGapRetainedCode CountableEnumeratedPartialStructure.prefixCode
  simp only [oneGapPartial, normalizedGraphModel, binaryUnaryAgeModel]
  rw [hBin, hE, hD]

/-- Equal finite ordinary tables suffice for equal entire retained L+ codes.
No equality outside the selected finite range is required. -/
theorem oneGapRetainedCode_eq_of_finite_graph
    (G H : Nat → Nat → Bool) (f g : Nat → Nat)
    (hf : StrictMono f) (hg : StrictMono g) (n : Nat)
    (hGraph : ∀ i < n, ∀ j < n, G (f i) (f j) = H (g i) (g j)) :
    oneGapRetainedCode G f n = oneGapRetainedCode H g n := by
  rw [oneGapRetainedCode_eq_prefix G f hf n,
    oneGapRetainedCode_eq_prefix H g hg n]
  have hBinary : (fun i j : Fin (2*n+1) => fun _ : Fin 1 =>
      oneGapEdge (fun a b => G (f a) (f b)) i.val j.val) =
      (fun i j : Fin (2*n+1) => fun _ : Fin 1 =>
        oneGapEdge (fun a b => H (g a) (g b)) i.val j.val) := by
    funext i j t
    by_cases hi : oneGapReal i.val
    · by_cases hj : oneGapReal j.val
      · have hil : oneGapIndex i.val < n := by
          have hBound := i.isLt
          have hAddr := oneGapAddress_index hi
          unfold oneGapAddress at hAddr
          omega
        have hjl : oneGapIndex j.val < n := by
          have hBound := j.isLt
          have hAddr := oneGapAddress_index hj
          unfold oneGapAddress at hAddr
          omega
        simpa only [oneGapEdge, hi, hj, and_self, ite_true] using
          hGraph (oneGapIndex i.val) hil (oneGapIndex j.val) hjl
      · simp [oneGapEdge, hj]
    · simp [oneGapEdge, hi]
  have hDiagonal := congrArg
    (fun B : Fin (2*n+1) → Fin (2*n+1) → Fin 1 → Bool => fun i t => B i i t)
    hBinary
  unfold CountableEnumeratedPartialStructure.prefixCode
  simp only [oneGapPartial, normalizedGraphModel, binaryUnaryAgeModel]
  rw [hBinary, hDiagonal]

end Kk
