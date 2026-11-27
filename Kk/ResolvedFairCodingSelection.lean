import Kk.ResolvedFairEventGeometry

/-!
# Finite selection of actual coding coordinates

English proof reviewed before implementation:
`docs/resolved_fair_coding_selection_english_20261127.md`.
The inverse correspondence is derived from actual singleton coding
certificates and the injective event-vertex enumeration. Auxiliary
retention remains an independent flag on whole event occurrences.
-/

namespace Kk

noncomputable def resolvedFairOriginalAddress
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  oneGapAddress (resolvedFairEventCodePosition s0 n)

theorem resolvedFairOriginalAddress_strictMono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    StrictMono (resolvedFairOriginalAddress s0) :=
  oneGapAddress_strictMono.comp (resolvedFairEventCodePosition_strictMono s0)

theorem resolvedFairVertexEventIndex_codePosition
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairVertexEventIndex s0 (resolvedFairEventCodePosition s0 n) =
      resolvedFairCodingEvent s0 n := by
  unfold resolvedFairVertexEventIndex resolvedFairEventCodePosition resolvedFairEventBoundary
  apply (oneGapBatchIndex_eq_iff _ (resolvedFairEventBlock_positive s0) _ _).mpr
  refine ⟨le_rfl, ?_⟩
  exact (oneGapBatchBoundary_strictMono _ (resolvedFairEventBlock_positive s0))
    (Nat.lt_succ_self _)

/-- The actual padded coding coordinate has the flag of its coding event. -/
theorem resolvedFairEventRole_originalAddress
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool) (n : Nat) :
    resolvedFairEventRole s0 keep (resolvedFairOriginalAddress s0 n) =
      .coded (keep (resolvedFairCodingEvent s0 n)) := by
  apply (resolvedFairEventRole_coded_iff s0 keep _ _).mpr
  refine ⟨oneGapAddress_real _, ?_, ?_⟩
  · simpa only [resolvedFairOriginalAddress, oneGapIndex_address,
      resolvedFairVertexEventIndex_codePosition] using (resolvedFairCodingEvent_spec s0 n).1
  · simp only [resolvedFairOriginalAddress, oneGapIndex_address,
      resolvedFairVertexEventIndex_codePosition]

/-- Every coded coordinate is the actual address of an original. The
coordinate equality is derived from its singleton certificate. -/
theorem resolvedFairEventRole_coded_iff_originalAddress
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (v : Nat) (b : Bool) :
    resolvedFairEventRole s0 keep v = .coded b ↔
      ∃ n : Nat, v = resolvedFairOriginalAddress s0 n ∧
        keep (resolvedFairCodingEvent s0 n) = b := by
  constructor
  · intro hCode
    obtain ⟨hReal, hKind, hFlag⟩ :=
      (resolvedFairEventRole_coded_iff s0 keep v b).mp hCode
    let k := resolvedFairVertexEventIndex s0 (oneGapIndex v)
    let n := (resolvedFairEventLocation s0 k).1
    have hBlock : (resolvedFairEvent s0 k).block = [2*n] :=
      (resolvedFairEvent_certificate s0 k).code_block hKind
    have hMem := resolvedFairEventVertex_mem_block s0 (oneGapIndex v)
    change resolvedFairEventVertex s0 (oneGapIndex v) ∈
      (resolvedFairEvent s0 k).block at hMem
    rw [hBlock] at hMem
    have hVertex : resolvedFairEventVertex s0 (oneGapIndex v) = 2*n := by
      simpa only [List.mem_singleton] using hMem
    have hIndex : oneGapIndex v = resolvedFairEventCodePosition s0 n :=
      resolvedFairEventVertex_injective s0 hEmpty
        (hVertex.trans (resolvedFairEventVertex_coded s0 n).symm)
    have hAddress : v = resolvedFairOriginalAddress s0 n := by
      calc
        v = oneGapAddress (oneGapIndex v) := (oneGapAddress_index hReal).symm
        _ = resolvedFairOriginalAddress s0 n := congrArg oneGapAddress hIndex
    have hEvent : k = resolvedFairCodingEvent s0 n := by
      dsimp only [k]
      rw [hIndex, resolvedFairVertexEventIndex_codePosition]
    refine ⟨n, hAddress, ?_⟩
    change keep k = b at hFlag
    rw [hEvent] at hFlag
    exact hFlag
  · rintro ⟨n, rfl, hFlag⟩
    rw [resolvedFairEventRole_originalAddress, hFlag]

theorem resolvedFairEventRole_coded_unique_originalAddress
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (v : Nat) (b : Bool)
    (hCode : resolvedFairEventRole s0 keep v = .coded b) :
    ∃! n : Nat, v = resolvedFairOriginalAddress s0 n ∧
      keep (resolvedFairCodingEvent s0 n) = b := by
  obtain ⟨n, hAddress, hFlag⟩ :=
    (resolvedFairEventRole_coded_iff_originalAddress s0 hEmpty keep v b).mp hCode
  refine ⟨n, ⟨hAddress, hFlag⟩, ?_⟩
  intro m hm
  exact (resolvedFairOriginalAddress_strictMono s0).injective
    (hm.1.symm.trans hAddress)

/-- Coding retention is determined by an actual finite set of original
indices. Auxiliary retention is a separate whole-event choice. -/
noncomputable def resolvedFairSelectedKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (k : Nat) : Bool :=
  if (resolvedFairEvent s0 k).kind = .code then
    decide (k ∈ S.image (resolvedFairCodingEvent s0))
  else auxKeep k

theorem resolvedFairSelectedKeep_code
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat) :
    resolvedFairSelectedKeep s0 S auxKeep (resolvedFairCodingEvent s0 n) =
      decide (n ∈ S) := by
  simp [resolvedFairSelectedKeep, (resolvedFairCodingEvent_spec s0 n).1,
    (resolvedFairCodingEvent_strictMono s0).injective.eq_iff]

theorem resolvedFairSelectedKeep_auxiliary
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (auxKeep : Nat → Bool) (k : Nat)
    (hAux : (resolvedFairEvent s0 k).kind ≠ .code) :
    resolvedFairSelectedKeep s0 S auxKeep k = auxKeep k := by
  simp [resolvedFairSelectedKeep, hAux]

/-- Exact identification with the selected original indices, including
the empty finite selection. No coordinate-image premise is assumed. -/
theorem resolvedFairSelectedRole_coded_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (v : Nat) :
    resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S auxKeep) v = .coded true ↔
      ∃ n ∈ S, v = resolvedFairOriginalAddress s0 n := by
  rw [resolvedFairEventRole_coded_iff_originalAddress s0 hEmpty]
  simp only [resolvedFairSelectedKeep_code, decide_eq_true_eq]
  constructor
  · rintro ⟨n, hAddress, hMem⟩
    exact ⟨n, hMem, hAddress⟩
  · rintro ⟨n, hMem, hAddress⟩
    exact ⟨n, hAddress, hMem⟩

/-- A finite ambient bound for every kept coding coordinate. -/
theorem resolvedFairSelectedRole_coded_bound
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (v : Nat)
    (hCode : resolvedFairEventRole s0 (resolvedFairSelectedKeep s0 S auxKeep) v =
      .coded true) :
    v < S.sup (resolvedFairOriginalAddress s0) + 1 := by
  obtain ⟨n, hMem, rfl⟩ :=
    (resolvedFairSelectedRole_coded_iff s0 hEmpty S auxKeep v).mp hCode
  have hLe := Finset.le_sup (f := resolvedFairOriginalAddress s0) hMem
  omega

/-- The complete original-address ordinary table, including its diagonal. -/
theorem resolvedFairOriginalAddress_edge
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) :
    oneGapEdge (resolvedFairEventEdge s0) (resolvedFairOriginalAddress s0 i)
      (resolvedFairOriginalAddress s0 j) = s0.edge (2*i) (2*j) := by
  unfold resolvedFairOriginalAddress
  rw [oneGapEdge_address]
  exact resolvedFairEventEdge_originals s0 i j

theorem resolvedInitialOriginalAddress_edge
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (i j : Nat) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    oneGapEdge (resolvedFairEventEdge s0) (resolvedFairOriginalAddress s0 i)
      (resolvedFairOriginalAddress s0 j) = E i j := by
  dsimp only
  rw [resolvedFairOriginalAddress_edge]
  change E (2*i/2) (2*j/2) = E i j
  congr 1 <;> omega

end Kk
