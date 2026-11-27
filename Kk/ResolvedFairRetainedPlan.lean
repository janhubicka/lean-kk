import Kk.ResolvedFairEventGeometry
import Kk.OneGapDummyCut

/-!
# A finite retained plan for the actual event schedule

Truncate at a kept coding original. The retained levels are complete
gap/vertex pairs for kept event positions, together with the anchor.
The ambient original pool contains every retained role in the prefix,
including dummy originals whose coordinates need not be retained levels.

English proof and independent review precede this implementation:
`docs/resolved_fair_retained_plan_english_audit_20261127.md`.
-/

namespace Kk

/-- A meaningful paired level records exactly its selected unpadded position. -/
theorem oneGapPairedLevels_address_iff (S : Finset Nat) (p : Nat) :
    oneGapAddress p ∈ oneGapPairedLevels S ↔ p ∈ S := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_insert.mp hp with hZero | hPair
    · unfold oneGapAddress at hZero
      omega
    · rcases Finset.mem_union.mp hPair with hGap | hVertex
      · obtain ⟨q, _hq, hEq⟩ := Finset.mem_image.mp hGap
        unfold oneGapAddress at hEq
        omega
      · obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hVertex
        exact oneGapAddress_strictMono.injective hEq ▸ hq
  · intro hp
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

/-- The padded coordinate of the coding cap. -/
noncomputable def resolvedFairRetainedTop
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  oneGapAddress (resolvedFairEventCodePosition s0 n)

/-- The finite ambient prefix includes the cap itself. -/
noncomputable def resolvedFairRetainedSize
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  resolvedFairRetainedTop s0 n + 1

/-- Kept vertex positions up to and including the coding cap position. -/
noncomputable def resolvedFairRetainedPositions
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : Finset Nat :=
  (Finset.range (resolvedFairEventCodePosition s0 n + 1)).filter
    (fun p => keep (resolvedFairVertexEventIndex s0 p) = true)

/-- Retain the anchor and both coordinates of each selected one-gap pair. -/
noncomputable def resolvedFairRetainedLevels
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : Finset Nat :=
  oneGapPairedLevels (resolvedFairRetainedPositions s0 keep n)

/-- The complete pool of retained-role originals in the finite prefix.
Dummy originals belong even when their own level is not retained. -/
def resolvedFairRetainedPool
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : Set (Fin (resolvedFairRetainedSize s0 n)) :=
  {v | ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val)}

/-- The actual last ambient name, whose retention is proved from its keep flag. -/
noncomputable def resolvedFairRetainedCap
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    Fin (resolvedFairRetainedSize s0 n) :=
  ⟨resolvedFairRetainedTop s0 n, Nat.lt_succ_self _⟩

theorem resolvedFairRetainedTop_lt_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairRetainedTop s0 n < resolvedFairRetainedSize s0 n :=
  Nat.lt_succ_self _

theorem resolvedFairRetainedPositions_mem_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n p : Nat) :
    p ∈ resolvedFairRetainedPositions s0 keep n ↔
      p ≤ resolvedFairEventCodePosition s0 n ∧
        keep (resolvedFairVertexEventIndex s0 p) = true := by
  simp only [resolvedFairRetainedPositions, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]

theorem resolvedFairRetainedLevels_finite
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : (resolvedFairRetainedLevels s0 keep n : Set Nat).Finite :=
  (resolvedFairRetainedLevels s0 keep n).finite_toSet

theorem resolvedFairRetainedPool_finite
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : (resolvedFairRetainedPool s0 keep n).Finite :=
  Set.toFinite _

theorem resolvedFairRetainedLevels_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) : 0 ∈ resolvedFairRetainedLevels s0 keep n :=
  oneGapPairedLevels_zero _

theorem resolvedFairRetainedLevels_bound
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n v : Nat) (hv : v ∈ resolvedFairRetainedLevels s0 keep n) :
    v ≤ resolvedFairRetainedTop s0 n := by
  classical
  rcases Finset.mem_insert.mp hv with hZero | hPair
  · subst v
    exact Nat.zero_le _
  · rcases Finset.mem_union.mp hPair with hGap | hVertex
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hGap
      have hBound := (resolvedFairRetainedPositions_mem_iff s0 keep n p).mp hp
      unfold resolvedFairRetainedTop oneGapAddress
      omega
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hVertex
      exact oneGapAddress_strictMono.monotone
        ((resolvedFairRetainedPositions_mem_iff s0 keep n p).mp hp).1

private theorem retainedPlan_role_real_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (v : Nat) (hReal : oneGapReal v) :
    ResolvedQRetainedBase (resolvedFairEventRole s0 keep v) ↔
      keep (resolvedFairVertexEventIndex s0 (oneGapIndex v)) = true := by
  simpa only [resolvedFairEventRole, resolvedFairVertexEventIndex,
    hReal, not_true_eq_false, false_or] using
    oneGapEventRole_retained_iff
      (fun k => (resolvedFairEventBlock s0 k).length)
      (resolvedFairEventBlock_positive s0)
      (fun k => decide ((resolvedFairEvent s0 k).kind = .code)) keep v

/-- Exact finite-level membership at meaningful coordinates. -/
theorem resolvedFairRetainedLevels_real_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n v : Nat) (hReal : oneGapReal v) :
    v ∈ resolvedFairRetainedLevels s0 keep n ↔
      v ≤ resolvedFairRetainedTop s0 n ∧
        ResolvedQRetainedBase (resolvedFairEventRole s0 keep v) := by
  have hAddress := oneGapAddress_index hReal
  have hMem : v ∈ resolvedFairRetainedLevels s0 keep n ↔
      oneGapIndex v ∈ resolvedFairRetainedPositions s0 keep n := by
    simpa only [resolvedFairRetainedLevels, hAddress] using
      oneGapPairedLevels_address_iff (resolvedFairRetainedPositions s0 keep n)
        (oneGapIndex v)
  have hBound : oneGapIndex v ≤ resolvedFairEventCodePosition s0 n ↔
      v ≤ resolvedFairRetainedTop s0 n := by
    unfold oneGapAddress at hAddress
    unfold resolvedFairRetainedTop oneGapAddress
    omega
  rw [hMem, resolvedFairRetainedPositions_mem_iff, hBound,
    ← retainedPlan_role_real_iff s0 keep v hReal]

/-- Every retained meaningful name below the cap is an actual paired level. -/
theorem resolvedFairRetainedLevels_of_retained_real
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n v : Nat) (hBound : v ≤ resolvedFairRetainedTop s0 n)
    (hReal : oneGapReal v)
    (hRetained : ResolvedQRetainedBase (resolvedFairEventRole s0 keep v)) :
    v ∈ resolvedFairRetainedLevels s0 keep n :=
  (resolvedFairRetainedLevels_real_iff s0 keep n v hReal).mpr ⟨hBound, hRetained⟩

/-- A meaningful omitted finite level has an omitted actual base role. -/
theorem resolvedFairRetainedLevels_omitted_real_not_retained
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n c : Nat) (hCut : c < resolvedFairRetainedTop s0 n)
    (hOmitted : c ∉ resolvedFairRetainedLevels s0 keep n)
    (hReal : oneGapReal c) :
    ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep c) := by
  intro hRetained
  exact hOmitted (resolvedFairRetainedLevels_of_retained_real s0 keep n c
    (Nat.le_of_lt hCut) hReal hRetained)

/-- In the finite prefix, a meaningful original is in the pool exactly
when its own coordinate is one of the paired retained levels. -/
theorem resolvedFairRetainedPool_real_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n))
    (hReal : oneGapReal v.val) :
    v ∈ resolvedFairRetainedPool s0 keep n ↔
      v.val ∈ resolvedFairRetainedLevels s0 keep n := by
  have hBound : v.val ≤ resolvedFairRetainedTop s0 n := by
    have hv := v.isLt
    unfold resolvedFairRetainedSize at hv
    omega
  change ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val) ↔ _
  rw [resolvedFairRetainedLevels_real_iff s0 keep n v.val hReal]
  simp only [hBound, true_and]

/-- Exact pool description, without identifying dummy roles with dummy levels. -/
theorem resolvedFairRetainedPool_mem_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n)) :
    v ∈ resolvedFairRetainedPool s0 keep n ↔
      ¬ oneGapReal v.val ∨ v.val ∈ resolvedFairRetainedLevels s0 keep n := by
  by_cases hReal : oneGapReal v.val
  · simpa only [hReal, not_true_eq_false, false_or] using
      resolvedFairRetainedPool_real_iff s0 keep n v hReal
  · have hDummy := (resolvedFairEventRole_dummy_iff s0 keep v.val).mpr hReal
    have hPool : v ∈ resolvedFairRetainedPool s0 keep n := Or.inl hDummy
    simp only [hPool, hReal, not_false_eq_true, true_or]

/-- Every retained level's ambient name is in the complete pool. -/
theorem resolvedFairRetainedPool_of_level
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v.val ∈ resolvedFairRetainedLevels s0 keep n) :
    v ∈ resolvedFairRetainedPool s0 keep n :=
  (resolvedFairRetainedPool_mem_iff s0 keep n v).mpr (Or.inr hv)

/-- The retained-parameter coverage premise required by the planned envelope.
The stronger preceding lemma does not need positive free level. -/
theorem resolvedFairRetainedPool_retained_parameters
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v.val ∈ resolvedFairRetainedLevels s0 keep n)
    (_hFree : 0 < ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel v.val) :
    v ∈ resolvedFairRetainedPool s0 keep n :=
  resolvedFairRetainedPool_of_level s0 keep n v hv

/-- Retained meaningful originals keep their actual preceding gap. -/
theorem resolvedFairRetainedPool_pair_retention
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v ∈ resolvedFairRetainedPool s0 keep n) (hReal : oneGapReal v.val) :
    v.val-1 ∈ resolvedFairRetainedLevels s0 keep n :=
  oneGapPairedLevels_preceding_gap _ v.val
    ((resolvedFairRetainedPool_real_iff s0 keep n v hReal).mp hv) hReal

/-- Every pool original has a retained free endpoint, including dummies. -/
theorem resolvedFairRetainedPool_freeLevel_mem
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v ∈ resolvedFairRetainedPool s0 keep n) :
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel v.val ∈
        resolvedFairRetainedLevels s0 keep n :=
  oneGap_freeLevel_mem_of_pair_retention (resolvedFairEventEdge s0)
    (resolvedFairRetainedSize s0 n) (resolvedFairRetainedLevels s0 keep n : Set Nat)
    (resolvedFairRetainedLevels_zero s0 keep n) v
    (resolvedFairRetainedPool_pair_retention s0 keep n v hv)

theorem resolvedFairRetainedPool_freeLevel_ne_of_omitted
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n c : Nat) (hOmitted : c ∉ resolvedFairRetainedLevels s0 keep n)
    (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v ∈ resolvedFairRetainedPool s0 keep n) :
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel v.val ≠ c := by
  intro hEq
  exact hOmitted (hEq ▸ resolvedFairRetainedPool_freeLevel_mem s0 keep n v hv)

private theorem retainedPlan_cap_event_index
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairVertexEventIndex s0 (resolvedFairEventCodePosition s0 n) =
      resolvedFairCodingEvent s0 n := by
  apply (oneGapBatchIndex_eq_iff
    (fun k => (resolvedFairEventBlock s0 k).length)
    (resolvedFairEventBlock_positive s0) _ _).mpr
  constructor
  · exact le_rfl
  · exact oneGapBatchBoundary_strictMono _ (resolvedFairEventBlock_positive s0)
      (Nat.lt_succ_self _)

private theorem retainedPlan_cap_role
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) :
    resolvedFairEventRole s0 keep (resolvedFairRetainedTop s0 n) =
      .coded (keep (resolvedFairCodingEvent s0 n)) := by
  apply (resolvedFairEventRole_coded_iff s0 keep _ _).mpr
  refine ⟨oneGapAddress_real _, ?_, ?_⟩
  · rw [show oneGapIndex (resolvedFairRetainedTop s0 n) =
        resolvedFairEventCodePosition s0 n by exact oneGapIndex_address _,
      retainedPlan_cap_event_index]
    exact (resolvedFairCodingEvent_spec s0 n).1
  · rw [show oneGapIndex (resolvedFairRetainedTop s0 n) =
        resolvedFairEventCodePosition s0 n by exact oneGapIndex_address _,
      retainedPlan_cap_event_index]

theorem resolvedFairRetainedPositions_cap
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true) :
    resolvedFairEventCodePosition s0 n ∈ resolvedFairRetainedPositions s0 keep n := by
  apply (resolvedFairRetainedPositions_mem_iff s0 keep n _).mpr
  exact ⟨le_rfl, (congrArg keep (retainedPlan_cap_event_index s0 n)).trans hCap⟩

theorem resolvedFairRetainedLevels_top
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true) :
    resolvedFairRetainedTop s0 n ∈ resolvedFairRetainedLevels s0 keep n :=
  (oneGapPairedLevels_address_iff _ _).mpr
    (resolvedFairRetainedPositions_cap s0 keep n hCap)

theorem resolvedFairRetainedCap_mem
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true) :
    resolvedFairRetainedCap s0 n ∈ resolvedFairRetainedPool s0 keep n := by
  apply Or.inr
  apply Or.inl
  exact (retainedPlan_cap_role s0 keep n).trans (congrArg ResolvedQBaseRole.coded hCap)

theorem resolvedFairRetainedLevels_cap_gap
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true) :
    resolvedFairRetainedTop s0 n - 1 ∈ resolvedFairRetainedLevels s0 keep n :=
  oneGapPairedLevels_preceding_gap _ _ (resolvedFairRetainedLevels_top s0 keep n hCap)
    (oneGapAddress_real _)

end Kk
