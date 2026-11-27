import Kk.ResolvedEventTrace

/-!
# Exact vertex sets and intermediate pools of actual event chains

English proof: `docs/resolved_event_schedule_english_20261127.md`.
Freshness is used at each event, so no ordering or disjointness of the
whole extracted list is assumed separately.
-/

namespace Kk

def resolvedEventVertices (events : List ResolvedEvent) : List Nat :=
  events.flatMap ResolvedEvent.block

theorem ResolvedEventChain.event_certificate {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    {e : ResolvedEvent} (he : e ∈ events) : ResolvedEventCertificate W r e := by
  induction h with
  | nil => simp at he
  | cons cert agreement tail ih =>
      rcases List.mem_cons.mp he with hEq | hMem
      · subst e
        exact cert
      · exact ih hMem

theorem ResolvedEventChain.event_postOld_subset {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    {e : ResolvedEvent} (he : e ∈ events) : e.postOld ⊆ Q := by
  induction h with
  | nil => simp at he
  | cons cert agreement tail ih =>
      rcases List.mem_cons.mp he with hEq | hMem
      · subst e
        exact tail.old_mono
      · exact ih hMem

theorem ResolvedEventChain.event_agreement {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    {e : ResolvedEvent} (he : e ∈ events)
    (x y : Nat) (hx : x ∈ e.postOld ∨ x ∈ W)
    (hy : y ∈ e.postOld ∨ y ∈ W) : E x y = e.edge x y := by
  induction h with
  | nil => simp at he
  | cons cert agreement tail ih =>
      rcases List.mem_cons.mp he with hEq | hMem
      · subst e
        exact agreement x y hx hy
      · exact ih hMem

/-- The flattened event list adds exactly the final pool minus the
initial pool; in particular it cannot repeat an initially old vertex. -/
theorem ResolvedEventChain.vertices_mem {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q) (v : Nat) :
    v ∈ resolvedEventVertices events ↔ v ∈ Q ∧ v ∉ P := by
  induction h with
  | nil => simp [resolvedEventVertices]
  | @cons e events Q cert agreement tail ih =>
      simp only [resolvedEventVertices,List.flatMap_cons,List.mem_append] at *
      have hFresh := Finset.disjoint_left.mp cert.block_fresh
      have hPost := tail.old_mono
      constructor
      · rintro (hv | hv)
        · have hb : v ∈ e.block.toFinset := List.mem_toFinset.mpr hv
          exact ⟨hPost (Finset.mem_union.mpr (Or.inr hb)),fun hp => hFresh hp hb⟩
        · obtain ⟨hQ,hNot⟩ := ih.mp hv
          exact ⟨hQ,fun hp => hNot (Finset.mem_union.mpr (Or.inl hp))⟩
      · rintro ⟨hQ,hNot⟩
        by_cases hb : v ∈ e.block
        · exact Or.inl hb
        · apply Or.inr
          apply ih.mpr
          refine ⟨hQ,?_⟩
          intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · exact hNot hp
          · exact hb (List.mem_toFinset.mp hp)

theorem ResolvedEventChain.vertices_nodup {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q) :
    (resolvedEventVertices events).Nodup := by
  induction h with
  | nil => simp [resolvedEventVertices]
  | @cons e events Q cert agreement tail ih =>
      change (e.block ++ resolvedEventVertices events).Nodup
      apply List.nodup_append'.mpr
      refine ⟨cert.block_nodup,ih,?_⟩
      intro v hv ht
      have hn := (tail.vertices_mem v).mp ht
      exact hn.2 (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hv)))

/-- Every actual event pre-pool is exactly the initial pool together
with the blocks of preceding event occurrences. -/
theorem ResolvedEventChain.preOld_iff {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    (i : Fin events.length) (v : Nat) :
    v ∈ (events[i.val]).preOld ↔ v ∈ P ∨
      ∃ j : Fin events.length, j.val < i.val ∧ v ∈ (events[j.val]).block := by
  induction h with
  | nil => exact Fin.elim0 i
  | @cons e events Q cert agreement tail ih =>
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
          simp only [Fin.val_succ,List.getElem_cons_succ]
          rw [ih i]
          constructor
          · rintro (hp | ⟨j,hji,hv⟩)
            · rcases Finset.mem_union.mp hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr ⟨0,by simp,List.mem_toFinset.mp hp⟩
            · exact Or.inr ⟨j.succ,by simpa using hji,by simpa using hv⟩
          · rintro (hp | ⟨j,hji,hv⟩)
            · exact Or.inl (Finset.mem_union.mpr (Or.inl hp))
            · cases j using Fin.cases with
              | zero =>
                  exact Or.inl (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hv)))
              | succ j =>
                  exact Or.inr ⟨j,by simpa using hji,by simpa using hv⟩

theorem ResolvedEventChain.blocks_disjoint {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    (i j : Fin events.length) (hij : i ≠ j) :
    List.Disjoint (events[i.val]).block (events[j.val]).block := by
  have hOrdered : ∀ a b : Fin events.length, a.val < b.val →
      List.Disjoint (events[a.val]).block (events[b.val]).block := by
    intro a b hab v ha hb
    have hp := (h.preOld_iff b v).mpr (Or.inr ⟨a,hab,ha⟩)
    have cert := h.event_certificate (List.getElem_mem b.isLt)
    exact (Finset.disjoint_left.mp cert.block_fresh) hp (List.mem_toFinset.mpr hb)
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hOrdered i j hlt
  · exact (hOrdered j i hgt).symm

end Kk
