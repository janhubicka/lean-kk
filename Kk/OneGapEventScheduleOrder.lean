import Kk.OneGapCountableSchedule

/-!
# Order and exact internal prefixes of chronological batches

English proof: `docs/resolved_event_schedule_english_20261127.md`.
These lemmas apply both to the finite event lists of rounds and to the
positive vertex blocks of the resulting countable event enumeration.
-/

namespace Kk

theorem oneGapBatchIndex_mono (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) : Monotone (oneGapBatchIndex size hPositive) := by
  intro i j hij
  have hi := oneGapBatchIndex_bounds size hPositive i
  have hj := oneGapBatchIndex_bounds size hPositive j
  by_contra hNot
  have hLe : oneGapBatchIndex size hPositive j + 1 ≤
      oneGapBatchIndex size hPositive i := by omega
  have hb := (oneGapBatchBoundary_strictMono size hPositive).monotone hLe
  omega

theorem oneGapBatchPosition_lt_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n)
    (x y : (n : Nat) × Fin (size n)) :
    oneGapBatchPosition size x < oneGapBatchPosition size y ↔
      x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2.val < y.2.val) := by
  rcases x with ⟨n,i⟩
  rcases y with ⟨m,j⟩
  have hn := oneGapBatchPosition_bounds size ⟨n,i⟩
  have hm := oneGapBatchPosition_bounds size ⟨m,j⟩
  dsimp only at hn hm ⊢
  have hMono := (oneGapBatchBoundary_strictMono size hPositive).monotone
  constructor
  · intro h
    by_cases hnm : n < m
    · exact Or.inl hnm
    · have hle : n ≤ m := by
        by_contra hnot
        have hb := hMono (show m+1 ≤ n by omega)
        omega
      have he : n = m := by omega
      refine Or.inr ⟨he,?_⟩
      subst m
      change oneGapBatchBoundary size n + i.val <
        oneGapBatchBoundary size n + j.val at h
      omega
  · rintro (h | ⟨h,hij⟩)
    · have hb := hMono (show n+1 ≤ m from h)
      omega
    · subst m
      change oneGapBatchBoundary size n + i.val <
        oneGapBatchBoundary size n + j.val
      omega

/-- The exact prefix before an entry: all preceding batches and the
strictly preceding entries of its own batch. -/
theorem oneGapChronologicalVertex_prefix_at_entry {α : Type*}
    (batch : Nat → List α) (hPositive : ∀ n, 0 < (batch n).length)
    (n : Nat) (i : Fin (batch n).length) (v : α) :
    (∃ k, k < oneGapBatchPosition (fun m => (batch m).length) ⟨n,i⟩ ∧
      oneGapChronologicalVertex batch hPositive k = v) ↔
      (∃ m, m < n ∧ v ∈ batch m) ∨
      ∃ j : Fin (batch n).length, j.val < i.val ∧ (batch n)[j.val] = v := by
  constructor
  · rintro ⟨k,hk,hkv⟩
    generalize hTag : oneGapBatchLocation (fun m => (batch m).length)
      hPositive k = tag
    rcases tag with ⟨m,j⟩
    have hPos : oneGapBatchPosition (fun m => (batch m).length) ⟨m,j⟩ = k := by
      rw [← hTag]
      exact oneGapBatchPosition_location _ hPositive k
    have hVal : (batch m)[j.val] = v := by
      change oneGapBatchValue batch ⟨m,j⟩ = v
      rw [← hTag]
      exact hkv
    have hOrder := (oneGapBatchPosition_lt_iff _ hPositive ⟨m,j⟩ ⟨n,i⟩).mp
      (show oneGapBatchPosition (fun m => (batch m).length) ⟨m,j⟩ <
        oneGapBatchPosition (fun m => (batch m).length) ⟨n,i⟩ by rw [hPos]; exact hk)
    change m < n ∨ (m = n ∧ j.val < i.val) at hOrder
    rcases hOrder with hmn | ⟨he,hji⟩
    · exact Or.inl ⟨m,hmn,hVal ▸ List.getElem_mem j.isLt⟩
    · subst m
      exact Or.inr ⟨j,hji,hVal⟩
  · rintro (⟨m,hm,hv⟩ | ⟨j,hj,hv⟩)
    · obtain ⟨j,hj,hVal⟩ := List.mem_iff_getElem.mp hv
      refine ⟨oneGapBatchPosition (fun m => (batch m).length) ⟨m,⟨j,hj⟩⟩,
        (oneGapBatchPosition_lt_iff _ hPositive _ _).mpr (Or.inl hm),?_⟩
      exact (oneGapChronologicalVertex_at_position batch hPositive m ⟨j,hj⟩).trans hVal
    · refine ⟨oneGapBatchPosition (fun m => (batch m).length) ⟨n,j⟩,
        (oneGapBatchPosition_lt_iff _ hPositive _ _).mpr (Or.inr ⟨rfl,hj⟩),?_⟩
      exact (oneGapChronologicalVertex_at_position batch hPositive n j).trans hv

end Kk
