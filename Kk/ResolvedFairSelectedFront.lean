import Kk.OneGapFiniteCodingFront
import Kk.ResolvedFairCodingSelection

/-!
# Finite selected fronts of the actual event graph

English proof and independent pre-code review:
`docs/finite_selected_front_english_20261127.md`.
The finite list is constructed. Actual graph geometry then supplies
positive-source coverage and the nonselected complete-old-column zero.
-/

namespace Kk
open SuccessorTree.V10

noncomputable def resolvedFairSelectedFrontSize
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) : Nat :=
  oneGapCodingFrontSize ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut

noncomputable def resolvedFairSelectedFront
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) :
    Fin (resolvedFairSelectedFrontSize s0 keep N V cut) → Nat :=
  oneGapCodingFrontSelected ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut

theorem resolvedFairSelectedFront_lt_size
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0 keep N V cut)) :
    resolvedFairSelectedFront s0 keep N V cut i < N :=
  oneGapCodingFrontSelected_lt_size
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut i

theorem resolvedFairSelectedFront_strictMono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) :
    StrictMono (resolvedFairSelectedFront s0 keep N V cut) :=
  oneGapCodingFrontSelected_strictMono
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut

theorem resolvedFairSelectedFront_range
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) (v : Fin N) :
    (∃ i, v.val = resolvedFairSelectedFront s0 keep N V cut i) ↔
      v ∈ V ∧ cut+1 ≤
        ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel v.val ∧
      resolvedFairEventRole s0 keep v.val = .coded true :=
  oneGapCodingFrontSelected_range
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 keep) V cut v

/-- The actual positive retained source is in the constructed selected list. -/
theorem resolvedFairSelectedFront_positive
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (N : Nat) (V : Set (Fin N))
    (hV : ∀ v ∈ V, ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val))
    (cut : Nat)
    (hOmitted : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep cut))
    (v : Fin N) (hv : v ∈ V)
    (hEligible : cut+1 ≤
      ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel v.val)
    (hEdge : oneGapEdge (resolvedFairEventEdge s0) cut v.val = true) :
    ∃ i, v.val = resolvedFairSelectedFront s0 keep N V cut i := by
  have hLater : cut < v.val :=
    lt_of_lt_of_le (Nat.lt_succ_self cut)
      (hEligible.trans
        (((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel_le v.val))
  have hCode := resolvedFairEvent_positive_retained_is_kept_coded
    s0 hEmpty keep cut v.val hLater hOmitted (hV v hv) hEdge
  exact (resolvedFairSelectedFront_range s0 keep N V cut v).mpr ⟨hv, hEligible, hCode⟩

/-- Absence from the actual selected list derives every old zero bit. -/
theorem resolvedFairSelectedFront_other_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (N : Nat) (V : Set (Fin N))
    (hV : ∀ v ∈ V, ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val))
    (cut : Nat)
    (hOmitted : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep cut))
    (v : Fin N) (hv : v ∈ V)
    (hEligible : cut+1 ≤
      ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel v.val)
    (hNotSelected : ¬ ∃ i, v.val = resolvedFairSelectedFront s0 keep N V cut i) :
    ∀ p, p < cut → oneGapEdge (resolvedFairEventEdge s0) p v.val = false := by
  have hLater : cut < v.val :=
    lt_of_lt_of_le (Nat.lt_succ_self cut)
      (hEligible.trans
        (((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel_le v.val))
  have hNotCode : resolvedFairEventRole s0 keep v.val ≠ .coded true := by
    intro hCode
    exact hNotSelected
      ((resolvedFairSelectedFront_range s0 keep N V cut v).mpr ⟨hv, hEligible, hCode⟩)
  exact resolvedFairEvent_later_retained_noncode_old_zero
    s0 hEmpty keep cut v.val hLater hOmitted (hV v hv) hNotCode

/-- The finite front contains precisely the eligible pool entries whose
original indices belong to the prescribed finite selection. -/
theorem resolvedFairSelectedFront_range_iff_original
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) (v : Fin N) :
    (∃ i, v.val = resolvedFairSelectedFront s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut i) ↔
      v ∈ V ∧ cut+1 ≤
        ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N).freeLevel v.val ∧
      ∃ n ∈ S, v.val = resolvedFairOriginalAddress s0 n := by
  rw [resolvedFairSelectedFront_range,
    resolvedFairSelectedRole_coded_iff s0 hEmpty S auxKeep v.val]

theorem resolvedFairSelectedFront_original
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat)
    (i : Fin (resolvedFairSelectedFrontSize s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut)) :
    ∃ n ∈ S, resolvedFairSelectedFront s0
      (resolvedFairSelectedKeep s0 S auxKeep) N V cut i = resolvedFairOriginalAddress s0 n := by
  apply (resolvedFairSelectedRole_coded_iff s0 hEmpty S auxKeep _).mp
  exact oneGapCodingFrontSelected_coded
    ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N)
    (resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S auxKeep)) V cut i

/-- A bound in terms of the prescribed original selection. A kept coded
cap must be included in S and is counted by this bound. -/
theorem resolvedFairSelectedFrontSize_le_card
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool)
    (N : Nat) (V : Set (Fin N)) (cut : Nat) :
    resolvedFairSelectedFrontSize s0 (resolvedFairSelectedKeep s0 S auxKeep) N V cut ≤
      S.card := by
  classical
  let A := (oneGapPartial (resolvedFairEventEdge s0)).finitePrefix N
  let role := resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S auxKeep)
  let C := oneGapCodingFrontSet A role V cut
  have hSub : C.image (fun v : Fin N => v.val) ⊆ S.image (resolvedFairOriginalAddress s0) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hCode := ((oneGapCodingFrontSet_mem A role V cut w).mp hw).2.2
    obtain ⟨n, hn, hEq⟩ :=
      (resolvedFairSelectedRole_coded_iff s0 hEmpty S auxKeep w.val).mp hCode
    exact Finset.mem_image.mpr ⟨n, hn, hEq.symm⟩
  calc
    resolvedFairSelectedFrontSize s0 (resolvedFairSelectedKeep s0 S auxKeep) N V cut = C.card := rfl
    _ = (C.image (fun v : Fin N => v.val)).card :=
      (Finset.card_image_of_injective C (fun _ _ h => Fin.ext h)).symm
    _ ≤ (S.image (resolvedFairOriginalAddress s0)).card := Finset.card_le_card hSub
    _ = S.card := Finset.card_image_of_injective S
      (resolvedFairOriginalAddress_strictMono s0).injective

end Kk
