import Kk.ResolvedEventTrace

/-!
# Birth edges of actual resolved events

The event certificate supplies the actual marker, cover or coding edge
table. Auxiliary events have zero edges to their complete pre-old pool;
no zero-edge premise is assumed. These facts concern the stored event
table and do not assert agreement on unused names with a later graph.

English proof and independent review:
`docs/resolved_event_birth_geometry_english_audit_20261127.md`.
-/

namespace Kk

/-- The stored edge table is the actual symmetric graph of the event. -/
theorem ResolvedEventCertificate.edge_sym {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) (x y : Nat) :
    e.edge x y = e.edge y x := by
  cases h with
  | marker s sort f hEven hSafe => exact (s.refineBatch sort f hEven hSafe).sym x y
  | cover s Q T hPQ hQW hBudget => exact (s.insertBlock Q T hPQ hQW hBudget).sym x y
  | code s => exact s.sym x y

theorem ResolvedEventCertificate.edge_loop {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) (x : Nat) :
    e.edge x x = false := by
  cases h with
  | marker s sort f hEven hSafe => exact (s.refineBatch sort f hEven hSafe).loops x
  | cover s Q T hPQ hQW hBudget => exact (s.insertBlock Q T hPQ hQW hBudget).loops x
  | code s => exact s.loops x

/-- A marker event introduces exactly its one concrete marker name. -/
theorem ResolvedEventCertificate.marker_block_singleton {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hMarker : e.kind = .marker) : ∃ q : Nat, e.block = [q] := by
  cases h with
  | marker s sort f hEven hSafe hExact i => exact ⟨resolvedMarkerName s.old i, rfl⟩
  | cover => simp at hMarker
  | code => simp at hMarker

/-- The code block is the prescribed original, without an ordering premise. -/
theorem ResolvedEventCertificate.code_block {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hCode : e.kind = .code) : e.block = [r] := by
  cases h with
  | marker => simp at hCode
  | cover => simp at hCode
  | code => rfl

/-- Every auxiliary block is outside the entire live set, not just a finite
sample of currently selected future names. -/
theorem ResolvedEventCertificate.auxiliary_block_not_live {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hAux : e.kind ≠ .code) (q : Nat) (hq : q ∈ e.block) : q ∉ W := by
  cases h with
  | marker s sort f hEven hSafe hExact i =>
      have hqEq : q = resolvedMarkerName s.old i := by simpa using hq
      rw [hqEq]
      exact resolvedMarkerName_not_live s.old W hEven i
  | cover s Q T hPQ hQW =>
      exact hQW q (by simpa using hq)
  | code => exact False.elim (hAux rfl)

/-- Auxiliary birth edges are zero in both directions on the complete
pre-old pool. A coding event is excluded because it can have old neighbours. -/
theorem ResolvedEventCertificate.auxiliary_old_zero {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hAux : e.kind ≠ .code) (p q : Nat)
    (hp : p ∈ e.preOld) (hq : q ∈ e.block) :
    e.edge p q = false ∧ e.edge q p = false := by
  classical
  have hForward : e.edge p q = false := by
    cases h with
    | marker s sort f hEven hSafe _hExact i hMixed R hR _hNot =>
        have hqEq : q = resolvedMarkerName s.old i := by simpa using hq
        subst q
        have hpW : p ∉ W := by
          rcases Finset.mem_union.mp hp with hpOld | hpR
          · exact s.separated p hpOld
          · obtain ⟨j, _hMixedJ, hName⟩ :=
              (mem_resolvedMarkerNames s.old W sort f p).mp (hR hpR)
            rw [← hName]
            exact resolvedMarkerName_not_live s.old W hEven j
        have hReverse : (s.refineBatch sort f hEven hSafe).edge
            (resolvedMarkerName s.old i) p = false := by
          change resolvedMarkerEdge s.edge s.old W sort f
            (resolvedMarkerName s.old i) p = false
          cases hBit : resolvedMarkerEdge s.edge s.old W sort f
              (resolvedMarkerName s.old i) p with
          | false => rfl
          | true =>
              exact False.elim (hpW
                ((resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hMixed p).mp hBit).1)
        exact ((s.refineBatch sort f hEven hSafe).sym p
          (resolvedMarkerName s.old i)).trans hReverse
    | cover s Q T hPQ hQW hBudget =>
        have hqQ : q ∈ Q := by simpa using hq
        have hpQ : p ∉ Q := fun hmem => (Finset.disjoint_left.mp hPQ) hp hmem
        have hpW := s.separated p hp
        change ResolvedLiveStage.blockEdge s.edge Q W _ T.1 p q = false
        simp [ResolvedLiveStage.blockEdge, hpQ, hqQ, hpW]
    | code => exact False.elim (hAux rfl)
  exact ⟨hForward, (h.edge_sym q p).trans hForward⟩

/-- Every actual event block is a directed clique. Marker and coding blocks
are singletons; cover blocks have the actual inserted clique edge table. -/
theorem ResolvedEventCertificate.block_clique {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) :
    IsDirectedCliqueOn e.edge e.block.toFinset := by
  cases h with
  | marker s sort f hEven hSafe hExact i =>
      intro x hx y hy hxy
      have hxEq : x = resolvedMarkerName s.old i := by simpa using hx
      have hyEq : y = resolvedMarkerName s.old i := by simpa using hy
      exact False.elim (hxy (hxEq.trans hyEq.symm))
  | cover s Q T hPQ hQW hBudget =>
      intro x hx y hy hxy
      have hxQ : x ∈ Q := by simpa using hx
      have hyQ : y ∈ Q := by simpa using hy
      change ResolvedLiveStage.blockEdge s.edge Q W _ T.1 x y = true
      simp [ResolvedLiveStage.blockEdge, hxQ, hyQ, hxy]
  | code =>
      intro x hx y hy hxy
      have hxEq : x = r := by simpa using hx
      have hyEq : y = r := by simpa using hy
      exact False.elim (hxy (hxEq.trans hyEq.symm))

/-- The actual cover block realizes its support on the entire live set,
in both ordinary directions. The old table on unused names is irrelevant. -/
theorem ResolvedLiveStage.insertBlock_live_bits {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell)
    (q v : Nat) (hq : q ∈ Q) (hv : v ∈ W) :
    (s.insertBlock Q T hPQ hQW hBudget).edge q v = decide (sort v ∈ T.1) ∧
      (s.insertBlock Q T hPQ hQW hBudget).edge v q = decide (sort v ∈ T.1) := by
  classical
  have hvQ : v ∉ Q := fun hmem => hQW v hmem hv
  change ResolvedLiveStage.blockEdge s.edge Q W sort T.1 q v = decide (sort v ∈ T.1) ∧
    ResolvedLiveStage.blockEdge s.edge Q W sort T.1 v q = decide (sort v ∈ T.1)
  simp [ResolvedLiveStage.blockEdge, hq, hvQ, hv]

/-- The actual marker-stage bit is precisely its original class/test rule. -/
theorem ResolvedBareStage.refineBatch_marker_positive_iff {d : Nat} {W : Set Nat}
    (s : ResolvedBareStage 4 W) (sort : Nat → Fin d) (f : Nat → Bool)
    (hEven : ∀ v ∈ W, v % 2 = 0)
    (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
      IsDirectedCliqueOn s.edge C → C.card < 3)
    (i : Fin d) (hMixed : ResolvedMixedClass W sort f i) (v : Nat) :
    (s.refineBatch sort f hEven hSafe).edge (resolvedMarkerName s.old i) v = true ↔
      v ∈ W ∧ sort v = i ∧ f v = true :=
  resolvedMarkerEdge_positive_iff s.edge s.old W sort f i hMixed v

/-- All members of one event block have the same ordinary live column.
This is a birth-table statement, before any later transport or projection. -/
theorem ResolvedEventCertificate.block_live_uniform {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (q q' v : Nat) (hq : q ∈ e.block) (hq' : q' ∈ e.block) (hv : v ∈ W) :
    e.edge q v = e.edge q' v := by
  cases h with
  | marker s sort f hEven hSafe hExact i =>
      have hqEq : q = resolvedMarkerName s.old i := by simpa using hq
      have hq'Eq : q' = resolvedMarkerName s.old i := by simpa using hq'
      rw [hqEq, hq'Eq]
  | cover s Q T hPQ hQW hBudget =>
      have hqQ : q ∈ Q := by simpa using hq
      have hq'Q : q' ∈ Q := by simpa using hq'
      exact (s.insertBlock_live_bits Q T hPQ hQW hBudget q v hqQ hv).1.trans
        (s.insertBlock_live_bits Q T hPQ hQW hBudget q' v hq'Q hv).1.symm
  | code =>
      have hqEq : q = r := by simpa using hq
      have hq'Eq : q' = r := by simpa using hq'
      rw [hqEq, hq'Eq]

end Kk
