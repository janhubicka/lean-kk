import Kk.ResolvedEventTrace

/-!
# Extract individual events from actual finite rounds

English proof: `docs/resolved_event_trace_english_20261127.md`.
Markers are serialized as singletons, covers in their recorded path
order, and coding last. The finite event list is proved to exist from
the actual witnesses; it is not an additional premise.
-/

namespace Kk

theorem ResolvedBareStage.refineBatch_exists_events {W : Set Nat} {d r : Nat}
    (s : ResolvedBareStage 4 W) (sort : Nat → Fin d) (f : Nat → Bool)
    (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3)
    (hExact : ResolvedClassExact s.edge s.old W sort) :
    ∃ events : List ResolvedEvent,
      ResolvedEventChain W r (s.refineBatch sort f hEven hSafe).edge
        s.old events (s.refineBatch sort f hEven hSafe).old ∧
      ∀ e ∈ events, e.kind = .marker := by
  classical
  let Q := resolvedMarkerNames s.old W sort f
  let t := s.refineBatch sort f hEven hSafe
  have hBuild : ∀ qs : List Nat, qs.Nodup → (∀ q ∈ qs, q ∈ Q) →
      ∀ R : Finset Nat, R ⊆ Q → Disjoint R qs.toFinset →
      ∃ events : List ResolvedEvent,
        ResolvedEventChain W r t.edge (s.old ∪ R) events
          (s.old ∪ (R ∪ qs.toFinset)) ∧
        ∀ e ∈ events, e.kind = .marker := by
    intro qs
    induction qs with
    | nil =>
        intro _hNodup _hMem R _hR _hDisj
        refine ⟨[], ?_, by simp⟩
        simpa using (ResolvedEventChain.nil (W := W) (r := r) (E := t.edge) (s.old ∪ R))
    | cons q qs ih =>
        intro hNodup hMem R hR hDisj
        have hq : q ∈ Q := hMem q (by simp)
        obtain ⟨i, hMixed, hName⟩ :=
          (mem_resolvedMarkerNames s.old W sort f q).mp hq
        subst q
        have hNot : resolvedMarkerName s.old i ∉ R := by
          intro hqR
          exact (Finset.disjoint_left.mp hDisj) hqR (by simp)
        have hR' : insert (resolvedMarkerName s.old i) R ⊆ Q := by
          intro x hx
          rcases Finset.mem_insert.mp hx with he | hx
          · subst x; exact hq
          · exact hR hx
        have hDisj' : Disjoint (insert (resolvedMarkerName s.old i) R) qs.toFinset := by
          apply Finset.disjoint_left.mpr
          intro x hx hy
          rcases Finset.mem_insert.mp hx with he | hx
          · subst x
            exact (List.nodup_cons.mp hNodup).1 (List.mem_toFinset.mp hy)
          · apply (Finset.disjoint_left.mp hDisj) hx
            simp only [List.mem_toFinset, List.mem_cons]
            exact Or.inr (List.mem_toFinset.mp hy)
        obtain ⟨events, hChain, hKinds⟩ := ih (List.nodup_cons.mp hNodup).2
          (fun x hx => hMem x (List.mem_cons_of_mem _ hx))
          (insert (resolvedMarkerName s.old i) R) hR' hDisj'
        let e : ResolvedEvent :=
          ⟨.marker, s.old ∪ R, [resolvedMarkerName s.old i], t.edge⟩
        have hPost : e.postOld = s.old ∪ insert (resolvedMarkerName s.old i) R := by
          ext x
          simp [e, ResolvedEvent.postOld]
        have hEnd : s.old ∪ (insert (resolvedMarkerName s.old i) R ∪ qs.toFinset) =
            s.old ∪ (R ∪ (resolvedMarkerName s.old i :: qs).toFinset) := by
          ext x
          simp
        have hTail : ResolvedEventChain W r t.edge e.postOld events
            (s.old ∪ (R ∪ (resolvedMarkerName s.old i :: qs).toFinset)) := by
          rw [hPost, ← hEnd]
          exact hChain
        refine ⟨e :: events, ?_, ?_⟩
        · exact .cons (.marker s sort f hEven hSafe hExact i hMixed R hR hNot)
            (by intros; rfl) hTail
        · intro a ha
          rcases List.mem_cons.mp ha with he | ha
          · subst a; rfl
          · exact hKinds a ha
  obtain ⟨events, hChain, hKinds⟩ := hBuild Q.sort (Finset.sort_nodup _ _)
    (fun q hq => by simpa only [Finset.mem_sort] using hq)
    ∅ (Finset.empty_subset _) (Finset.disjoint_empty_left _)
  refine ⟨events, ?_, hKinds⟩
  change ResolvedEventChain W r t.edge s.old events (s.old ∪ Q)
  simpa only [Finset.empty_union, Finset.union_empty, Finset.sort_toFinset] using hChain

theorem ResolvedMarkerBatchStep.old_mono {W : Set Nat}
    {s t : ResolvedBareStage 4 W} {f : Nat → Bool}
    (h : ResolvedMarkerBatchStep s t f) : s.old ⊆ t.old := by
  obtain ⟨d, sort, hEven, hSafe, _hExact, rfl⟩ := h
  exact Finset.subset_union_left

theorem ResolvedMarkerBatchStep.preserves {W : Set Nat}
    {s t : ResolvedBareStage 4 W} {f : Nat → Bool}
    (h : ResolvedMarkerBatchStep s t f) :
    ∀ x y : Nat, (x ∈ s.old ∨ x ∈ W) → (y ∈ s.old ∨ y ∈ W) →
      t.edge x y = s.edge x y := by
  obtain ⟨d, sort, hEven, hSafe, _hExact, rfl⟩ := h
  exact s.refineBatch_preserves sort f hEven hSafe

theorem ResolvedMarkerBatchStep.exists_events {W : Set Nat} {r : Nat}
    {s t : ResolvedBareStage 4 W} {f : Nat → Bool}
    (h : ResolvedMarkerBatchStep s t f) :
    ∃ events : List ResolvedEvent,
      ResolvedEventChain W r t.edge s.old events t.old ∧
      ∀ e ∈ events, e.kind = .marker := by
  obtain ⟨d, sort, hEven, hSafe, hExact, rfl⟩ := h
  exact s.refineBatch_exists_events sort f hEven hSafe hExact

theorem ResolvedLiveCoverPath.exists_events {d r : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    {s t : ResolvedLiveStage d 4 W sort}
    (h : ResolvedLiveCoverPath W sort s t)
    (hExact : ResolvedClassExact s.edge s.old W sort) :
    ∃ events : List ResolvedEvent,
      ResolvedEventChain W r t.edge s.old events t.old ∧
      ∀ e ∈ events, e.kind = .cover := by
  revert hExact
  induction h with
  | stop s =>
      intro _
      exact ⟨[], .nil _, by simp⟩
  | advance s Q T hPQ hQW hBudget hCover hChanged hMinimal hSize tail ih =>
      intro hExact
      have hExact' : ResolvedClassExact
          (s.insertBlock Q T hPQ hQW hBudget).edge
          (s.insertBlock Q T hPQ hQW hBudget).old W sort :=
        resolvedClassExact_of_live_extension s
          (s.insertBlock Q T hPQ hQW hBudget) hExact
          Finset.subset_union_left
          (s.insertBlock_preserves_live Q T hPQ hQW hBudget)
      obtain ⟨events, hChain, hKinds⟩ := ih hExact'
      let e : ResolvedEvent :=
        ⟨.cover, s.old, Q.sort, (s.insertBlock Q T hPQ hQW hBudget).edge⟩
      have hPost : e.postOld = (s.insertBlock Q T hPQ hQW hBudget).old := by
        simp [e, ResolvedEvent.postOld, ResolvedLiveStage.insertBlock]
      have hTail := hChain
      rw [← hPost] at hTail
      refine ⟨e :: events, .cons
        (.cover s Q T hPQ hQW hBudget hCover hChanged hMinimal hSize hExact) ?_ hTail, ?_⟩
      · intro x y hx hy
        apply tail.preserves x y
        · simpa only [ResolvedEvent.postOld, Finset.sort_toFinset,
            ResolvedLiveStage.insertBlock] using hx
        · simpa only [ResolvedEvent.postOld, Finset.sort_toFinset,
            ResolvedLiveStage.insertBlock] using hy
      · intro a ha
        rcases List.mem_cons.mp ha with he | ha
        · subst a; rfl
        · exact hKinds a ha

/-- The actual round witnesses supply a finite list of individual
events. Every cover retains its path order, and coding is the last
singleton. Earlier event graphs agree with the final graph only on
their actual post-old/live domains. -/
theorem ResolvedRoundResult.exists_events {W W' : Set Nat}
    {s : ResolvedBareStage 4 W} {r : Nat} {t : ResolvedBareStage 4 W'}
    (h : ResolvedRoundResult s r t) (hr : r ∈ W) :
    ∃ (aux : List ResolvedEvent) (code : ResolvedEvent),
      ResolvedEventChain W r t.edge s.old (aux ++ [code]) t.old ∧
      (∀ e ∈ aux, e.kind ≠ .code) ∧ code.kind = .code ∧ code.block = [r] := by
  classical
  obtain ⟨s1, s2, d, sort, a, b, hSplit0, hSplit1, hBare,
    hPath, hExactA, hSat, hExact, hSingleton, hConst, _hNext, hEdge, hOld⟩ := h.trace
  obtain ⟨events0, hEvents0, hKinds0⟩ := hSplit0.exists_events (r := r)
  obtain ⟨events1, hEvents1, hKinds1⟩ := hSplit1.exists_events (r := r)
  obtain ⟨covers, hCovers, hKindsC⟩ := hPath.exists_events (r := r) hExactA
  have hOldA : a.old = s2.old := congrArg ResolvedBareStage.old hBare
  have hEdgeA : a.edge = s2.edge := congrArg ResolvedBareStage.edge hBare
  have hKeep2 : ∀ x y : Nat, (x ∈ s2.old ∨ x ∈ W) →
      (y ∈ s2.old ∨ y ∈ W) → b.edge x y = s2.edge x y := by
    intro x y hx hy
    have hxA : x ∈ a.old ∨ x ∈ W := by simpa only [hOldA] using hx
    have hyA : y ∈ a.old ∨ y ∈ W := by simpa only [hOldA] using hy
    exact (hPath.preserves x y hxA hyA).trans (congrFun (congrFun hEdgeA x) y)
  have hKeep1 : ∀ x y : Nat, (x ∈ s1.old ∨ x ∈ W) →
      (y ∈ s1.old ∨ y ∈ W) → b.edge x y = s1.edge x y := by
    intro x y hx hy
    exact (hKeep2 x y (hx.imp (fun hp => hSplit1.old_mono hp) id)
      (hy.imp (fun hp => hSplit1.old_mono hp) id)).trans (hSplit1.preserves x y hx hy)
  have hCovers' : ResolvedEventChain W r b.edge s2.old covers b.old := by
    simpa only [hOldA] using hCovers
  let code : ResolvedEvent := ⟨.code, b.old, [r], b.edge⟩
  have hPost : code.postOld = insert r b.old := by
    ext x
    simp [code, ResolvedEvent.postOld]
  have hCode : ResolvedEventChain W r b.edge b.old [code] (insert r b.old) := by
    refine .cons (.code b hr hSat hExact hSingleton hConst) (by intros; rfl) ?_
    rw [hPost]
    exact .nil _
  let aux := events0 ++ events1 ++ covers
  have hAll := ((hEvents0.transport hKeep1).append
    (hEvents1.transport hKeep2)).append hCovers'
  have hFinal := hAll.append hCode
  refine ⟨aux, code, ?_, ?_, rfl, rfl⟩
  · simpa only [aux, hEdge, hOld, List.append_assoc] using hFinal
  · intro e he
    simp only [aux, List.mem_append, or_assoc] at he
    rcases he with he | he | he
    · simp [hKinds0 e he]
    · simp [hKinds1 e he]
    · simp [hKindsC e he]

end Kk
