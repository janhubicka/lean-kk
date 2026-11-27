import Kk.ResolvedFairRetainedPlan
import Kk.ResolvedFairSelectedFront

/-!
# A finite requested selection with a fresh actual coding cap

English proof reviewed before implementation:
`docs/resolved_fair_finite_selection_english_20261127.md`.
The cap is constructed beyond every requested original and is explicitly
included in the coding selection. Auxiliary retention remains arbitrary.
-/

namespace Kk

/-- A fresh original index beyond every member of the requested selection. -/
def resolvedFairSelectionCap (S : Finset Nat) : Nat :=
  S.sup id + 1

/-- The cap is part of the actual coding selection and its cardinality. -/
def resolvedFairSelectionWithCap (S : Finset Nat) : Finset Nat :=
  insert (resolvedFairSelectionCap S) S

/-- Coding flags use the augmented selection; auxiliary flags are unchanged. -/
noncomputable def resolvedFairFiniteKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) : Nat → Bool :=
  resolvedFairSelectedKeep s0 (resolvedFairSelectionWithCap S) auxKeep

theorem resolvedFairSelection_lt_cap
    (S : Finset Nat) (n : Nat) (hn : n ∈ S) :
    n < resolvedFairSelectionCap S := by
  have hLe : n ≤ S.sup id := Finset.le_sup (f := id) hn
  exact Nat.lt_succ_of_le hLe

theorem resolvedFairSelectionCap_not_mem (S : Finset Nat) :
    resolvedFairSelectionCap S ∉ S := by
  intro hMem
  exact (Nat.lt_irrefl _) (resolvedFairSelection_lt_cap S _ hMem)

theorem resolvedFairSelectionWithCap_card (S : Finset Nat) :
    (resolvedFairSelectionWithCap S).card = S.card + 1 := by
  exact Finset.card_insert_of_notMem (resolvedFairSelectionCap_not_mem S)

theorem resolvedFairSelectionWithCap_le_cap
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    n ≤ resolvedFairSelectionCap S := by
  rcases Finset.mem_insert.mp hn with rfl | hn
  · exact le_rfl
  · exact Nat.le_of_lt (resolvedFairSelection_lt_cap S n hn)

theorem resolvedFairFiniteKeep_code
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat) :
    resolvedFairFiniteKeep s0 S auxKeep (resolvedFairCodingEvent s0 n) =
      decide (n ∈ resolvedFairSelectionWithCap S) :=
  resolvedFairSelectedKeep_code s0 (resolvedFairSelectionWithCap S) auxKeep n

theorem resolvedFairFiniteKeep_cap
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) :
    resolvedFairFiniteKeep s0 S auxKeep
      (resolvedFairCodingEvent s0 (resolvedFairSelectionCap S)) = true := by
  rw [resolvedFairFiniteKeep_code]
  simp only [resolvedFairSelectionWithCap, Finset.mem_insert_self, decide_true]

/-- Every augmented original, including the cap, has selected coding role. -/
theorem resolvedFairFiniteSelection_role
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat)
    (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairEventRole s0 (resolvedFairFiniteKeep s0 S auxKeep)
      (resolvedFairOriginalAddress s0 n) = .coded true := by
  rw [resolvedFairEventRole_originalAddress, resolvedFairFiniteKeep_code]
  simp only [hn, decide_true]

/-- Requested original addresses lie strictly below the fresh cap. -/
theorem resolvedFairFiniteSelection_address_lt_top
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (n : Nat) (hn : n ∈ S) :
    resolvedFairOriginalAddress s0 n <
      resolvedFairRetainedTop s0 (resolvedFairSelectionCap S) :=
  (resolvedFairOriginalAddress_strictMono s0) (resolvedFairSelection_lt_cap S n hn)

/-- Augmented original addresses are at most the cap, with equality allowed. -/
theorem resolvedFairFiniteSelection_address_le_top
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairOriginalAddress s0 n ≤
      resolvedFairRetainedTop s0 (resolvedFairSelectionCap S) :=
  (resolvedFairOriginalAddress_strictMono s0).monotone
    (resolvedFairSelectionWithCap_le_cap S n hn)

theorem resolvedFairFiniteSelection_address_lt_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairOriginalAddress s0 n <
      resolvedFairRetainedSize s0 (resolvedFairSelectionCap S) :=
  Nat.lt_succ_of_le (resolvedFairFiniteSelection_address_le_top s0 S n hn)

/-- The actual finite-prefix name of an augmented selected original. -/
noncomputable def resolvedFairFiniteSelectionVertex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    Fin (resolvedFairRetainedSize s0 (resolvedFairSelectionCap S)) :=
  ⟨resolvedFairOriginalAddress s0 n,
    resolvedFairFiniteSelection_address_lt_size s0 S n hn⟩

@[simp] theorem resolvedFairFiniteSelectionVertex_val
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    (resolvedFairFiniteSelectionVertex s0 S n hn).val =
      resolvedFairOriginalAddress s0 n := rfl

theorem resolvedFairFiniteSelection_mem_levels
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat)
    (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairOriginalAddress s0 n ∈
      resolvedFairRetainedLevels s0 (resolvedFairFiniteKeep s0 S auxKeep)
        (resolvedFairSelectionCap S) := by
  apply resolvedFairRetainedLevels_of_retained_real
    s0 (resolvedFairFiniteKeep s0 S auxKeep) (resolvedFairSelectionCap S)
    (resolvedFairOriginalAddress s0 n)
    (resolvedFairFiniteSelection_address_le_top s0 S n hn) (oneGapAddress_real _)
  exact Or.inr (Or.inl (resolvedFairFiniteSelection_role s0 S auxKeep n hn))

theorem resolvedFairFiniteSelection_mem_pool
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat)
    (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairFiniteSelectionVertex s0 S n hn ∈
      resolvedFairRetainedPool s0 (resolvedFairFiniteKeep s0 S auxKeep)
        (resolvedFairSelectionCap S) := by
  exact resolvedFairRetainedPool_of_level
    s0 (resolvedFairFiniteKeep s0 S auxKeep) (resolvedFairSelectionCap S)
    (resolvedFairFiniteSelectionVertex s0 S n hn)
    (resolvedFairFiniteSelection_mem_levels s0 S auxKeep n hn)

/-- The selected coding cap is counted by the extra one, for every finite pool. -/
theorem resolvedFairFiniteSelectedFrontSize_le_card
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) :
    resolvedFairSelectedFrontSize s0 (resolvedFairFiniteKeep s0 S auxKeep) N V cut ≤
      S.card + 1 := by
  exact (resolvedFairSelectedFrontSize_le_card s0 hEmpty
    (resolvedFairSelectionWithCap S) auxKeep N V cut).trans_eq
      (resolvedFairSelectionWithCap_card S)

end Kk
