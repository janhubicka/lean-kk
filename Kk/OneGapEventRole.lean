import Kk.OneGapCountableSchedule
import Kk.OneGapFullClosure

/-!
# Roles of chronological event occurrences under one-gap padding

Positive event sizes determine a unique global event index at every
unpadded position. Coding and retention flags are constant on each event.
An auxiliary block is identified by that global occurrence index.

The resulting roles have uniform block flags and are convex modulo
the isolated dummy coordinates. No graph-edge claim is made here.

English proof and independent review precede this implementation:
`docs/one_gap_event_role_english_audit_20261127.md`.
-/

namespace Kk

/-- Meaningful coordinates inherit the flags of their global event
occurrence; the anchor and every gap are dummy coordinates. -/
def oneGapEventRole (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (v : Nat) : ResolvedQBaseRole :=
  if oneGapReal v then
    let n := oneGapBatchIndex size hPositive (oneGapIndex v)
    if isCode n = true then .coded (keep n) else .auxiliary n (keep n)
  else .dummy

theorem oneGapEventRole_of_not_real (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (v : Nat) (hv : ¬ oneGapReal v) :
    oneGapEventRole size hPositive isCode keep v = .dummy := by
  simp [oneGapEventRole, hv]

@[simp] theorem oneGapEventRole_zero (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) :
    oneGapEventRole size hPositive isCode keep 0 = .dummy := by
  exact oneGapEventRole_of_not_real size hPositive isCode keep 0
    (by simp [oneGapReal])

@[simp] theorem oneGapEventRole_gap (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) (i : Nat) :
    oneGapEventRole size hPositive isCode keep (2*i+1) = .dummy := by
  apply oneGapEventRole_of_not_real
  unfold oneGapReal
  omega

/-- Exact role at the meaningful position of an unpadded vertex. -/
theorem oneGapEventRole_address (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) (i : Nat) :
    oneGapEventRole size hPositive isCode keep (oneGapAddress i) =
      if isCode (oneGapBatchIndex size hPositive i) = true then
        .coded (keep (oneGapBatchIndex size hPositive i))
      else .auxiliary (oneGapBatchIndex size hPositive i)
        (keep (oneGapBatchIndex size hPositive i)) := by
  simp only [oneGapEventRole, oneGapAddress_real, ite_true, oneGapIndex_address]

/-- Every tagged entry of an event has that event's exact role and flag. -/
theorem oneGapEventRole_batchPosition (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (n : Nat) (i : Fin (size n)) :
    oneGapEventRole size hPositive isCode keep
        (oneGapAddress (oneGapBatchPosition size ⟨n,i⟩)) =
      if isCode n = true then .coded (keep n) else .auxiliary n (keep n) := by
  have hn : oneGapBatchIndex size hPositive (oneGapBatchPosition size ⟨n,i⟩) = n :=
    (oneGapBatchIndex_eq_iff size hPositive _ n).mpr
      (oneGapBatchPosition_bounds size ⟨n,i⟩)
  rw [oneGapEventRole_address, hn]

/-- Exactly the anchor and gaps are dummy roles. -/
theorem oneGapEventRole_dummy_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) (v : Nat) :
    oneGapEventRole size hPositive isCode keep v = .dummy ↔ ¬ oneGapReal v := by
  by_cases hv : oneGapReal v
  · by_cases hc : isCode (oneGapBatchIndex size hPositive (oneGapIndex v)) = true <;>
      simp [oneGapEventRole, hv, hc]
  · simp [oneGapEventRole, hv]

/-- Auxiliary identities include the global event index, so equal supports
or round-local labels cannot identify two different event occurrences. -/
theorem oneGapEventRole_auxiliary_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (v n : Nat) (b : Bool) :
    oneGapEventRole size hPositive isCode keep v = .auxiliary n b ↔
      oneGapReal v ∧ oneGapBatchIndex size hPositive (oneGapIndex v) = n ∧
        isCode n = false ∧ keep n = b := by
  by_cases hv : oneGapReal v
  · constructor
    · intro hRole
      cases hc : isCode (oneGapBatchIndex size hPositive (oneGapIndex v)) with
      | false =>
          have hEq : ResolvedQBaseRole.auxiliary
              (oneGapBatchIndex size hPositive (oneGapIndex v))
              (keep (oneGapBatchIndex size hPositive (oneGapIndex v))) =
                .auxiliary n b := by
            simpa [oneGapEventRole, hv, hc] using hRole
          have hPair := ResolvedQBaseRole.auxiliary.inj hEq
          refine ⟨hv, hPair.1, ?_, ?_⟩
          · exact hPair.1 ▸ hc
          · exact hPair.1 ▸ hPair.2
      | true => simp [oneGapEventRole, hv, hc] at hRole
    · rintro ⟨_hv, hn, hc, hk⟩
      simp [oneGapEventRole, hv, hn, hc, hk]
  · simp [oneGapEventRole, hv]

/-- A meaningful vertex is retained exactly when its event is kept.
Every dummy is a retained base role, independently of finite level sets. -/
theorem oneGapEventRole_retained_iff (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) (v : Nat) :
    ResolvedQRetainedBase (oneGapEventRole size hPositive isCode keep v) ↔
      ¬ oneGapReal v ∨ keep (oneGapBatchIndex size hPositive (oneGapIndex v)) = true := by
  by_cases hv : oneGapReal v
  · cases hc : isCode (oneGapBatchIndex size hPositive (oneGapIndex v)) <;>
      cases hk : keep (oneGapBatchIndex size hPositive (oneGapIndex v)) <;>
      simp [oneGapEventRole, ResolvedQRetainedBase, hv, hc, hk]
  · simp [oneGapEventRole, ResolvedQRetainedBase, hv]

theorem oneGapEventRole_retained_batchPosition (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (n : Nat) (i : Fin (size n)) :
    ResolvedQRetainedBase (oneGapEventRole size hPositive isCode keep
      (oneGapAddress (oneGapBatchPosition size ⟨n,i⟩))) ↔ keep n = true := by
  have hn : oneGapBatchIndex size hPositive (oneGapBatchPosition size ⟨n,i⟩) = n :=
    (oneGapBatchIndex_eq_iff size hPositive _ n).mpr
      (oneGapBatchPosition_bounds size ⟨n,i⟩)
  simpa only [oneGapAddress_real, not_true_eq_false, false_or,
    oneGapIndex_address, hn] using
    oneGapEventRole_retained_iff size hPositive isCode keep
      (oneGapAddress (oneGapBatchPosition size ⟨n,i⟩))

/-- The exact whole-block flag premise of the retained-pool geometry. -/
theorem oneGapEventRole_block_flag (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool)
    (i j block : Nat) (a b : Bool)
    (hi : oneGapEventRole size hPositive isCode keep i = .auxiliary block a)
    (hj : oneGapEventRole size hPositive isCode keep j = .auxiliary block b) :
    a = b := by
  have hI := (oneGapEventRole_auxiliary_iff size hPositive isCode keep i block a).mp hi
  have hJ := (oneGapEventRole_auxiliary_iff size hPositive isCode keep j block b).mp hj
  exact hI.2.2.2.symm.trans hJ.2.2.2

/-- Contiguous event blocks remain convex after the isolated gap before
each meaningful vertex is inserted. This is the exact full-pool premise. -/
theorem oneGapEventRole_block_convex (size : Nat → Nat)
    (hPositive : ∀ n, 0 < size n) (isCode keep : Nat → Bool) :
    OneGapBlockConvex (oneGapEventRole size hPositive isCode keep) := by
  intro a b c block hab hbc ha hc
  by_cases hb : oneGapReal b
  · right
    obtain ⟨hRealA, hIndexA, hCode, hKeep⟩ :=
      (oneGapEventRole_auxiliary_iff size hPositive isCode keep a block true).mp ha
    obtain ⟨hRealC, hIndexC, _hCodeC, _hKeepC⟩ :=
      (oneGapEventRole_auxiliary_iff size hPositive isCode keep c block true).mp hc
    have hA := oneGapAddress_index hRealA
    have hB := oneGapAddress_index hb
    have hC := oneGapAddress_index hRealC
    unfold oneGapAddress at hA hB hC
    have hab' : oneGapIndex a ≤ oneGapIndex b := by omega
    have hbc' : oneGapIndex b ≤ oneGapIndex c := by omega
    have hIndexB : oneGapBatchIndex size hPositive (oneGapIndex b) = block :=
      oneGapBatchLocation_convex size hPositive
        (oneGapIndex a) (oneGapIndex b) (oneGapIndex c) block
        hab' hbc' hIndexA hIndexC
    exact (oneGapEventRole_auxiliary_iff size hPositive isCode keep b block true).mpr
      ⟨hb, hIndexB, hCode, hKeep⟩
  · left
    exact oneGapEventRole_of_not_real size hPositive isCode keep b hb

end Kk
