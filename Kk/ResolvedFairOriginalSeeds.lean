import Kk.ResolvedFairSelectedEnvelope

/-!
# Full original seeds in the actual finite retained pool

English proof reviewed before implementation:
`docs/all_auxiliary_envelope_english_20261127.md`.
Full original types have their actual retained free levels. This does
not claim retained levels for arbitrary proper prefixes of those types.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

/-- The genuine admissible original type of a name in the finite prefix. -/
noncomputable def resolvedFairOriginalType
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n)) :
    AdmissibleKptNode (hensonForbiddenFamily 4 (by omega)) :=
  ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
    (resolvedFairRetainedSize s0 n)).kptOriginal
    (hensonForbiddenFamily 4 (by omega))
    (oneGap_finitePrefix_avoids (resolvedFairEventEdge s0) 4 (by omega)
      (resolvedFairEventGraph_avoids s0 hEmpty) (resolvedFairRetainedSize s0 n)) v

noncomputable def resolvedFairOriginalSeeds
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (U : Set (Fin (resolvedFairRetainedSize s0 n))) :
    Set (AdmissibleKptNode (hensonForbiddenFamily 4 (by omega))) :=
  resolvedFairOriginalType s0 hEmpty n '' U

theorem resolvedFairOriginalType_level
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n)) :
    LevelTree.lev (resolvedFairOriginalType s0 hEmpty n v) =
      ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
        (resolvedFairRetainedSize s0 n)).freeLevel v.val := rfl

/-- A full original is a prefix of itself in its own source pool. -/
theorem resolvedFairOriginalSeeds_pool
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (U : Set (Fin (resolvedFairRetainedSize s0 n))) :
    resolvedFairOriginalSeeds s0 hEmpty n U ⊆
      ambientPrefixPool (hensonForbiddenFamily 4 (by omega))
        ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix (resolvedFairRetainedSize s0 n))
        (oneGap_finitePrefix_avoids (resolvedFairEventEdge s0) 4 (by omega)
          (resolvedFairEventGraph_avoids s0 hEmpty) (resolvedFairRetainedSize s0 n)) U := by
  rintro z ⟨v, hv, rfl⟩
  exact ⟨resolvedFairOriginalType s0 hEmpty n v, ⟨v, hv, rfl⟩, le_rfl⟩

theorem resolvedFairOriginalSeeds_bounded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (U : Set (Fin (resolvedFairRetainedSize s0 n))) :
    resolvedFairOriginalSeeds s0 hEmpty n U ⊆ levelLe (resolvedFairRetainedTop s0 n) := by
  rintro z ⟨v, _hv, rfl⟩
  change LevelTree.lev (resolvedFairOriginalType s0 hEmpty n v) ≤ _
  rw [resolvedFairOriginalType_level]
  have hFree := ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
    (resolvedFairRetainedSize s0 n)).freeLevel_le v.val
  have hSize := v.isLt
  change v.val < resolvedFairRetainedTop s0 n + 1 at hSize
  omega

theorem resolvedFairOriginalSeeds_retained
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n : Nat)
    (U : Set (Fin (resolvedFairRetainedSize s0 n)))
    (hUV : U ⊆ resolvedFairRetainedPool s0 keep n) :
    ∀ z ∈ resolvedFairOriginalSeeds s0 hEmpty n U,
      LevelTree.lev z ∈ resolvedFairRetainedLevels s0 keep n := by
  rintro z ⟨v, hv, rfl⟩
  rw [resolvedFairOriginalType_level]
  exact resolvedFairRetainedPool_freeLevel_mem s0 keep n v (hUV hv)

theorem resolvedFairOriginalSeeds_finite
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (U : Set (Fin (resolvedFairRetainedSize s0 n))) :
    (resolvedFairOriginalSeeds s0 hEmpty n U).Finite :=
  (Set.toFinite U).image (resolvedFairOriginalType s0 hEmpty n)

/-- The actual typed addresses of the requested originals and their cap. -/
noncomputable def resolvedFairFiniteOriginalPool
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) :
    Set (Fin (resolvedFairRetainedSize s0 (resolvedFairSelectionCap S))) :=
  {v | ∃ n ∈ resolvedFairSelectionWithCap S, v.val = resolvedFairOriginalAddress s0 n}

noncomputable def resolvedFairFiniteOriginalSeeds
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (by omega))) :=
  resolvedFairOriginalSeeds s0 hEmpty (resolvedFairSelectionCap S)
    (resolvedFairFiniteOriginalPool s0 S)

theorem resolvedFairFiniteOriginalPool_retained
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) :
    resolvedFairFiniteOriginalPool s0 S ⊆
      resolvedFairRetainedPool s0 (resolvedFairFiniteKeep s0 S auxKeep)
        (resolvedFairSelectionCap S) := by
  rintro v ⟨n, hn, hAddress⟩
  have hv : v = resolvedFairFiniteSelectionVertex s0 S n hn := Fin.ext hAddress
  rw [hv]
  exact resolvedFairFiniteSelection_mem_pool s0 S auxKeep n hn

/-- Every augmented selected original occurs among the constructed seeds. -/
theorem resolvedFairFiniteSelectionType_mem_seeds
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (n : Nat) (hn : n ∈ resolvedFairSelectionWithCap S) :
    resolvedFairOriginalType s0 hEmpty (resolvedFairSelectionCap S)
      (resolvedFairFiniteSelectionVertex s0 S n hn) ∈
        resolvedFairFiniteOriginalSeeds s0 hEmpty S :=
  ⟨resolvedFairFiniteSelectionVertex s0 S n hn, ⟨n, hn, rfl⟩, rfl⟩

end Kk
