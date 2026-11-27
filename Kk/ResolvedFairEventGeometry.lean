import Kk.ResolvedFairEventSchedule
import Kk.ResolvedEventBirthGeometry
import Kk.OneGapEventRole

/-!
# Ordinary geometry of the actual chronological event graph

Exact pre-old prefixes and actual birth certificates derive the ordinary
graph premises used by full retained-pool geometry. No old-zero or
different-block nonedge premise is supplied by the caller.

English proof and independent review precede this implementation:
`docs/resolved_fair_event_geometry_english_audit_20261127.md`.
-/

namespace Kk

/-- The global event occurrence containing an unpadded vertex position. -/
noncomputable def resolvedFairVertexEventIndex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i : Nat) : Nat :=
  oneGapBatchIndex (fun k => (resolvedFairEventBlock s0 k).length)
    (resolvedFairEventBlock_positive s0) i

theorem resolvedFairVertexEventIndex_mono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    Monotone (resolvedFairVertexEventIndex s0) :=
  oneGapBatchIndex_mono _ (resolvedFairEventBlock_positive s0)

theorem resolvedFairEventVertex_mem_block
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i : Nat) :
    resolvedFairEventVertex s0 i ∈
      (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 i)).block :=
  oneGapChronologicalVertex_mem (resolvedFairEventBlock s0)
    (resolvedFairEventBlock_positive s0) i

/-- The actual limit has no edge from an earlier event's block to a
later auxiliary event's block, in either ordinary direction. -/
theorem resolvedFairEvent_auxiliary_prior_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (a b p q : Nat) (hab : a < b)
    (hAux : (resolvedFairEvent s0 b).kind ≠ .code)
    (hp : p ∈ (resolvedFairEvent s0 a).block)
    (hq : q ∈ (resolvedFairEvent s0 b).block) :
    resolvedFairEdge s0 p q = false ∧ resolvedFairEdge s0 q p = false := by
  have hpOld : p ∈ (resolvedFairEvent s0 b).preOld :=
    (resolvedFairEvent_preOld_iff s0 hEmpty b p).mpr ⟨a, hab, hp⟩
  have hZero := (resolvedFairEvent_certificate s0 b).auxiliary_old_zero
    hAux p q hpOld hq
  have hpPost : p ∈ (resolvedFairEvent s0 b).postOld :=
    Finset.mem_union.mpr (Or.inl hpOld)
  have hqPost : q ∈ (resolvedFairEvent s0 b).postOld :=
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hq))
  exact ⟨(resolvedFairEvent_agreement s0 b p q (Or.inl hpPost) (Or.inl hqPost)).trans
      hZero.1,
    (resolvedFairEvent_agreement s0 b q p (Or.inl hqPost) (Or.inl hpPost)).trans hZero.2⟩

/-- The same birth fact in actual chronological vertex coordinates. -/
theorem resolvedFairEventEdge_auxiliary_prior_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (i j : Nat)
    (hOrder : resolvedFairVertexEventIndex s0 i < resolvedFairVertexEventIndex s0 j)
    (hAux : (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 j)).kind ≠ .code) :
    resolvedFairEventEdge s0 i j = false ∧ resolvedFairEventEdge s0 j i = false :=
  resolvedFairEvent_auxiliary_prior_zero s0 hEmpty
    (resolvedFairVertexEventIndex s0 i) (resolvedFairVertexEventIndex s0 j)
    (resolvedFairEventVertex s0 i) (resolvedFairEventVertex s0 j) hOrder hAux
    (resolvedFairEventVertex_mem_block s0 i) (resolvedFairEventVertex_mem_block s0 j)

/-- Different auxiliary occurrences are anticomplete, independent of
their essential supports or the order of the two queried vertices. -/
theorem resolvedFairEventEdge_distinct_auxiliary_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (i j : Nat)
    (hAuxI : (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 i)).kind ≠ .code)
    (hAuxJ : (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 j)).kind ≠ .code)
    (hDifferent : resolvedFairVertexEventIndex s0 i ≠ resolvedFairVertexEventIndex s0 j) :
    resolvedFairEventEdge s0 i j = false := by
  rcases lt_or_gt_of_ne hDifferent with hlt | hgt
  · exact (resolvedFairEventEdge_auxiliary_prior_zero s0 hEmpty i j hlt hAuxJ).1
  · exact (resolvedFairEventEdge_auxiliary_prior_zero s0 hEmpty j i hgt hAuxI).2

/-- Roles of the actual event stream with one keep flag per global event.
Auxiliary identifiers are occurrence indices, not essential supports. -/
noncomputable def resolvedFairEventRole
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool) :
    Nat → ResolvedQBaseRole :=
  oneGapEventRole (fun k => (resolvedFairEventBlock s0 k).length)
    (resolvedFairEventBlock_positive s0)
    (fun k => decide ((resolvedFairEvent s0 k).kind = .code)) keep

theorem resolvedFairEventRole_dummy_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool) (v : Nat) :
    resolvedFairEventRole s0 keep v = .dummy ↔ ¬ oneGapReal v :=
  oneGapEventRole_dummy_iff _ (resolvedFairEventBlock_positive s0) _ keep v

theorem resolvedFairEventRole_auxiliary_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (v n : Nat) (b : Bool) :
    resolvedFairEventRole s0 keep v = .auxiliary n b ↔
      oneGapReal v ∧ resolvedFairVertexEventIndex s0 (oneGapIndex v) = n ∧
        (resolvedFairEvent s0 n).kind ≠ .code ∧ keep n = b := by
  simpa [resolvedFairEventRole, resolvedFairVertexEventIndex] using
    oneGapEventRole_auxiliary_iff (fun k => (resolvedFairEventBlock s0 k).length)
      (resolvedFairEventBlock_positive s0)
      (fun k => decide ((resolvedFairEvent s0 k).kind = .code)) keep v n b

theorem resolvedFairEventRole_coded_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (v : Nat) (b : Bool) :
    resolvedFairEventRole s0 keep v = .coded b ↔
      oneGapReal v ∧
        (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 (oneGapIndex v))).kind = .code ∧
        keep (resolvedFairVertexEventIndex s0 (oneGapIndex v)) = b := by
  let n := resolvedFairVertexEventIndex s0 (oneGapIndex v)
  change (if oneGapReal v then
      if decide ((resolvedFairEvent s0 n).kind = .code) = true then
        ResolvedQBaseRole.coded (keep n) else .auxiliary n (keep n)
    else .dummy) = .coded b ↔
      oneGapReal v ∧ (resolvedFairEvent s0 n).kind = .code ∧ keep n = b
  by_cases hv : oneGapReal v <;>
    by_cases hCode : (resolvedFairEvent s0 n).kind = .code <;>
    simp [hv, hCode]

theorem resolvedFairEventRole_block_flag
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (i j block : Nat) (a b : Bool)
    (hi : resolvedFairEventRole s0 keep i = .auxiliary block a)
    (hj : resolvedFairEventRole s0 keep j = .auxiliary block b) : a = b :=
  oneGapEventRole_block_flag _ (resolvedFairEventBlock_positive s0) _ keep
    i j block a b hi hj

theorem resolvedFairEventRole_block_convex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool) :
    OneGapBlockConvex (resolvedFairEventRole s0 keep) :=
  oneGapEventRole_block_convex _ (resolvedFairEventBlock_positive s0) _ keep

/-- Dummy rows of the actual padded graph vanish by the padding definition. -/
theorem resolvedFairEvent_dummy_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (i j : Nat) (hi : resolvedFairEventRole s0 keep i = .dummy) :
    oneGapEdge (resolvedFairEventEdge s0) i j = false := by
  have hNot := (resolvedFairEventRole_dummy_iff s0 keep i).mp hi
  simp [oneGapEdge, hNot]

/-- Earlier coding coordinates cannot lie in the same event as a later
auxiliary coordinate. Monotone event indices therefore give a strict
event order, and actual auxiliary birth geometry gives the nonedge. -/
theorem resolvedFairEvent_coded_aux_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (i j : Nat) (selected : Bool) (block : Nat) (retained : Bool)
    (hij : i < j)
    (hi : resolvedFairEventRole s0 keep i = .coded selected)
    (hj : resolvedFairEventRole s0 keep j = .auxiliary block retained) :
    oneGapEdge (resolvedFairEventEdge s0) i j = false := by
  obtain ⟨hRealI, hCode, _hSelected⟩ :=
    (resolvedFairEventRole_coded_iff s0 keep i selected).mp hi
  obtain ⟨hRealJ, hIndexJ, hAux, _hRetained⟩ :=
    (resolvedFairEventRole_auxiliary_iff s0 keep j block retained).mp hj
  have hInv : oneGapIndex i ≤ oneGapIndex j := by
    have hI := oneGapAddress_index hRealI
    have hJ := oneGapAddress_index hRealJ
    unfold oneGapAddress at hI hJ
    omega
  have hLe := resolvedFairVertexEventIndex_mono s0 hInv
  have hNe : resolvedFairVertexEventIndex s0 (oneGapIndex i) ≠
      resolvedFairVertexEventIndex s0 (oneGapIndex j) := by
    intro hSame
    apply hAux
    rw [← hIndexJ, ← hSame]
    exact hCode
  have hLt : resolvedFairVertexEventIndex s0 (oneGapIndex i) <
      resolvedFairVertexEventIndex s0 (oneGapIndex j) := by omega
  have hAuxJ :
      (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 (oneGapIndex j))).kind ≠ .code := by
    simpa only [hIndexJ] using hAux
  have hZero := (resolvedFairEventEdge_auxiliary_prior_zero s0 hEmpty
    (oneGapIndex i) (oneGapIndex j) hLt hAuxJ).1
  simpa [oneGapEdge, hRealI, hRealJ] using hZero

/-- The different-block premise for the actual padded graph and actual
event-occurrence roles, with both possible chronological orders covered. -/
theorem resolvedFairEvent_distinct_aux_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (i j p q : Nat) (a b : Bool) (hpq : p ≠ q)
    (hi : resolvedFairEventRole s0 keep i = .auxiliary p a)
    (hj : resolvedFairEventRole s0 keep j = .auxiliary q b) :
    oneGapEdge (resolvedFairEventEdge s0) i j = false := by
  obtain ⟨hRealI, hIndexI, hAuxI, _hKeepI⟩ :=
    (resolvedFairEventRole_auxiliary_iff s0 keep i p a).mp hi
  obtain ⟨hRealJ, hIndexJ, hAuxJ, _hKeepJ⟩ :=
    (resolvedFairEventRole_auxiliary_iff s0 keep j q b).mp hj
  have hDifferent : resolvedFairVertexEventIndex s0 (oneGapIndex i) ≠
      resolvedFairVertexEventIndex s0 (oneGapIndex j) := by
    simpa only [hIndexI, hIndexJ] using hpq
  have hAuxI' :
      (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 (oneGapIndex i))).kind ≠ .code := by
    simpa only [hIndexI] using hAuxI
  have hAuxJ' :
      (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 (oneGapIndex j))).kind ≠ .code := by
    simpa only [hIndexJ] using hAuxJ
  have hZero := resolvedFairEventEdge_distinct_auxiliary_zero s0 hEmpty
    (oneGapIndex i) (oneGapIndex j) hAuxI' hAuxJ' hDifferent
  simpa [oneGapEdge, hRealI, hRealJ] using hZero

/-- Actual later retained auxiliaries have zero complete old columns at
an omitted base role. Every graph and block premise is derived above;
selected-age neutrality and projected diary legality remain separate. -/
theorem resolvedFairEvent_later_retained_aux_old_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (i cut j block : Nat)
    (hi : i < cut) (hj : cut < j)
    (hOmitted : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep cut))
    (hJ : resolvedFairEventRole s0 keep j = .auxiliary block true) :
    oneGapEdge (resolvedFairEventEdge s0) i j = false :=
  oneGap_later_retained_aux_old_zero
    (resolvedFairEventRole s0 keep) (oneGapEdge (resolvedFairEventEdge s0))
    (resolvedFairEvent_dummy_zero s0 keep)
    (resolvedFairEvent_coded_aux_zero s0 hEmpty keep)
    (resolvedFairEvent_distinct_aux_zero s0 hEmpty keep)
    (resolvedFairEventRole_block_flag s0 keep)
    (resolvedFairEventRole_block_convex s0 keep)
    i cut j block hi hj hOmitted hJ

/-- Positive later retained neighbours of an omitted role are kept
coding vertices. This identifies a role, not a finite selected list. -/
theorem resolvedFairEvent_positive_retained_is_kept_coded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (i j : Nat) (hij : i < j)
    (hOmitted : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep i))
    (hRetained : ResolvedQRetainedBase (resolvedFairEventRole s0 keep j))
    (hEdge : oneGapEdge (resolvedFairEventEdge s0) i j = true) :
    resolvedFairEventRole s0 keep j = .coded true := by
  have hClassify : ∀ r : ResolvedQBaseRole,
      ¬ ResolvedQRetainedBase r → ResolvedQOmittedBase r := by
    intro r hNot
    cases r with
    | dummy => exact Or.inl rfl
    | coded b => exact Or.inr (Or.inl ⟨b, rfl⟩)
    | auxiliary block b =>
        cases b with
        | false => exact Or.inr (Or.inr ⟨block, rfl⟩)
        | true => exact False.elim (hNot (Or.inr (Or.inr ⟨block, rfl⟩)))
  have hSym : ∀ x y, oneGapEdge (resolvedFairEventEdge s0) x y =
      oneGapEdge (resolvedFairEventEdge s0) y x := by
    intro x y
    by_cases hx : oneGapReal x <;> by_cases hy : oneGapReal y <;>
      simp [oneGapEdge, hx, hy, resolvedFairEventEdge_sym]
  exact resolvedQ_omitted_base_positive_retained_is_selected_coding
    (resolvedFairEventRole s0 keep) (oneGapEdge (resolvedFairEventEdge s0))
    hSym (resolvedFairEvent_dummy_zero s0 keep)
    (resolvedFairEvent_coded_aux_zero s0 hEmpty keep)
    (resolvedFairEvent_distinct_aux_zero s0 hEmpty keep)
    (resolvedFairEventRole_block_flag s0 keep)
    i j hij (hClassify _ hOmitted) hRetained hEdge

/-- A later retained role other than kept coding is dummy or kept
auxiliary, so its complete old ordinary column at an omitted role is zero.
No identification with a finite selected terminal list is assumed. -/
theorem resolvedFairEvent_later_retained_noncode_old_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (cut j : Nat) (hj : cut < j)
    (hOmitted : ¬ ResolvedQRetainedBase (resolvedFairEventRole s0 keep cut))
    (hRetained : ResolvedQRetainedBase (resolvedFairEventRole s0 keep j))
    (hNotCode : resolvedFairEventRole s0 keep j ≠ .coded true) :
    ∀ i, i < cut → oneGapEdge (resolvedFairEventEdge s0) i j = false := by
  intro i hi
  rcases hRetained with hDummy | hCode | ⟨block, hAux⟩
  · have hNotReal := (resolvedFairEventRole_dummy_iff s0 keep j).mp hDummy
    simp [oneGapEdge, hNotReal]
  · exact False.elim (hNotCode hCode)
  · exact resolvedFairEvent_later_retained_aux_old_zero s0 hEmpty keep
      i cut j block hi hj hOmitted hAux

end Kk
