import Kk.ResolvedLiveRound
import Mathlib.Data.Finset.Sort

/-!
# Certificates for actual individual resolved events

English proof and independent review:
`docs/resolved_event_trace_english_20261127.md`.
An event retains its actual post-event edge table. A chain compares
that table with its reference graph only on the actual post-old pool
and the round's live set; unused names need not agree.
-/

namespace Kk

inductive ResolvedEventKind where
  | marker
  | cover
  | code
  deriving DecidableEq

structure ResolvedEvent where
  kind : ResolvedEventKind
  preOld : Finset Nat
  block : List Nat
  edge : Nat → Nat → Bool

def ResolvedEvent.postOld (e : ResolvedEvent) : Finset Nat :=
  e.preOld ∪ e.block.toFinset

/-- The constructors retain the actual witnesses, rather than only
a partition of the final old pool. `W` is the live set before coding. -/
inductive ResolvedEventCertificate (W : Set Nat) (r : Nat) :
    ResolvedEvent → Prop where
  | marker {d : Nat} (s : ResolvedBareStage 4 W)
      (sort : Nat → Fin d) (f : Nat → Bool)
      (hEven : ∀ v ∈ W, v % 2 = 0)
      (hSafe : ∀ C : Finset Nat, (∀ x ∈ C, x ∈ W ∧ f x = true) →
        IsDirectedCliqueOn s.edge C → C.card < 3)
      (hExact : ResolvedClassExact s.edge s.old W sort)
      (i : Fin d) (hMixed : ResolvedMixedClass W sort f i)
      (R : Finset Nat) (hR : R ⊆ resolvedMarkerNames s.old W sort f)
      (hNot : resolvedMarkerName s.old i ∉ R) :
      ResolvedEventCertificate W r
        ⟨.marker, s.old ∪ R, [resolvedMarkerName s.old i],
          (s.refineBatch sort f hEven hSafe).edge⟩
  | cover {d : Nat} {sort : Nat → Fin d} (s : ResolvedLiveStage d 4 W sort)
      (Q : Finset Nat) (T : IntegerGraphSupport d 4)
      (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
      (hBudget : Q.card + s.futureAge T < 4)
      (hCover : AgeCover (IsIntegerGraphAge d 4)
        (s.insertBlock Q T hPQ hQW hBudget).oldAge s.oldAge)
      (hChanged : (s.insertBlock Q T hPQ hQW hBudget).oldAge T < s.oldAge T)
      (hMinimal : ∀ U : IntegerGraphSupport d 4, U.1 ⊆ T.1 → U.1 ≠ T.1 →
        (s.insertBlock Q T hPQ hQW hBudget).oldAge U = s.oldAge U)
      (hSize : 4 = (s.insertBlock Q T hPQ hQW hBudget).oldAge T + Q.card + 1) :
      ResolvedEventCertificate W r
        ⟨.cover, s.old, Q.sort, (s.insertBlock Q T hPQ hQW hBudget).edge⟩
  | code {d : Nat} {sort : Nat → Fin d} (s : ResolvedLiveStage d 4 W sort)
      (hr : r ∈ W) (hSat : s.oldAge = s.futureAge)
      (hExact : ResolvedClassExact s.edge s.old W sort)
      (hSingleton : ∀ v ∈ W, sort v = sort r → v = r)
      (hConst : ∀ v ∈ W, ∀ w ∈ W, sort v = sort w → s.edge r v = s.edge r w) :
      ResolvedEventCertificate W r ⟨.code, s.old, [r], s.edge⟩

theorem ResolvedLiveStage.insertBlock_empty_oldAge {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old ∅) (hQW : ∀ q ∈ (∅ : Finset Nat), q ∉ W)
    (hBudget : (∅ : Finset Nat).card + s.futureAge T < ell) :
    (s.insertBlock ∅ T hPQ hQW hBudget).oldAge = s.oldAge := by
  classical
  have hEdge : ResolvedLiveStage.blockEdge s.edge ∅ W sort T.1 = s.edge := by
    funext x y
    simp [ResolvedLiveStage.blockEdge]
  have hColumn : supportBlockOldColumn ∅ T.1 s.column = s.column := by
    funext p i
    simp [supportBlockOldColumn]
  simp only [ResolvedLiveStage.oldAge, ResolvedLiveStage.insertBlock,
    Finset.union_empty, hEdge, hColumn]

theorem resolvedCoverBlock_nonempty {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort) (Q : Finset Nat)
    (T : IntegerGraphSupport d ell) (hPQ : Disjoint s.old Q)
    (hQW : ∀ q ∈ Q, q ∉ W) (hBudget : Q.card + s.futureAge T < ell)
    (hChanged : (s.insertBlock Q T hPQ hQW hBudget).oldAge T < s.oldAge T) :
    Q.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hQ
  subst Q
  rw [s.insertBlock_empty_oldAge T hPQ hQW hBudget] at hChanged
  exact (Nat.lt_irrefl _) hChanged

theorem ResolvedEventCertificate.block_pos {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) :
    0 < e.block.length := by
  cases h with
  | marker => simp
  | cover s Q T hPQ hQW hBudget _hCover hChanged _hMinimal _hSize =>
      simpa only [Finset.length_sort] using
        Finset.card_pos.mpr (resolvedCoverBlock_nonempty s Q T hPQ hQW hBudget hChanged)
  | code => simp

theorem ResolvedEventCertificate.block_nodup {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) :
    e.block.Nodup := by
  cases h with
  | marker => simp
  | cover => exact Finset.sort_nodup _ _
  | code => simp

theorem ResolvedEventCertificate.block_fresh {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) :
    Disjoint e.preOld e.block.toFinset := by
  cases h with
  | marker s sort f hEven hSafe hExact i hMixed R hR hNot =>
      apply Finset.disjoint_left.mpr
      intro x hx hq
      have he : x = resolvedMarkerName s.old i := by simpa using hq
      subst x
      rcases Finset.mem_union.mp hx with hp | hp
      · exact resolvedMarkerName_not_old s.old i hp
      · exact hNot hp
  | cover s Q T hPQ => simpa using hPQ
  | code s hr =>
      apply Finset.disjoint_left.mpr
      intro x hx hq
      have he : x = r := by simpa using hq
      subst x
      exact s.separated r hx hr

/-- The edge table in each event stays unchanged when the reference
graph changes. Agreement is confined to its actual post-old/live domain. -/
inductive ResolvedEventChain (W : Set Nat) (r : Nat) (E : Nat → Nat → Bool) :
    Finset Nat → List ResolvedEvent → Finset Nat → Prop where
  | nil (P : Finset Nat) : ResolvedEventChain W r E P [] P
  | cons {e : ResolvedEvent} {events : List ResolvedEvent} {Q : Finset Nat}
      (certificate : ResolvedEventCertificate W r e)
      (agreement : ∀ x y : Nat, (x ∈ e.postOld ∨ x ∈ W) →
        (y ∈ e.postOld ∨ y ∈ W) → E x y = e.edge x y)
      (tail : ResolvedEventChain W r E e.postOld events Q) :
      ResolvedEventChain W r E e.preOld (e :: events) Q

theorem ResolvedEventChain.old_mono {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q) : P ⊆ Q := by
  induction h with
  | nil => exact Finset.Subset.refl _
  | cons _ _ _ ih => exact Finset.subset_union_left.trans ih

theorem ResolvedEventChain.append {W : Set Nat} {r : Nat}
    {E : Nat → Nat → Bool} {P Q R : Finset Nat}
    {events more : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    (hMore : ResolvedEventChain W r E Q more R) :
    ResolvedEventChain W r E P (events ++ more) R := by
  induction h with
  | nil => exact hMore
  | cons hCert hAgree _ ih => exact .cons hCert hAgree (ih hMore)

theorem ResolvedEventChain.transport {W : Set Nat} {r : Nat}
    {E E' : Nat → Nat → Bool} {P Q : Finset Nat} {events : List ResolvedEvent}
    (h : ResolvedEventChain W r E P events Q)
    (hKeep : ∀ x y : Nat, (x ∈ Q ∨ x ∈ W) → (y ∈ Q ∨ y ∈ W) →
      E' x y = E x y) :
    ResolvedEventChain W r E' P events Q := by
  induction h with
  | nil => exact .nil _
  | cons hCert hAgree hTail ih =>
      refine .cons hCert ?_ (ih hKeep)
      intro x y hx hy
      exact (hKeep x y (hx.imp (fun hp => hTail.old_mono hp) id)
        (hy.imp (fun hp => hTail.old_mono hp) id)).trans (hAgree x y hx hy)

theorem ResolvedLiveCoverPath.old_mono {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    {s t : ResolvedLiveStage d ell W sort}
    (h : ResolvedLiveCoverPath W sort s t) : s.old ⊆ t.old := by
  induction h with
  | stop => exact Finset.Subset.refl _
  | advance _ _ _ _ _ _ _ _ _ _ _ ih =>
      exact Finset.subset_union_left.trans ih

theorem ResolvedLiveCoverPath.preserves {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    {s t : ResolvedLiveStage d ell W sort}
    (h : ResolvedLiveCoverPath W sort s t) :
    ∀ x y : Nat, (x ∈ s.old ∨ x ∈ W) → (y ∈ s.old ∨ y ∈ W) →
      t.edge x y = s.edge x y := by
  induction h with
  | stop => intros; rfl
  | advance s Q T hPQ hQW hBudget _hCover _hChanged _hMinimal _hSize _tail ih =>
      intro x y hx hy
      have hx' : x ∈ (s.insertBlock Q T hPQ hQW hBudget).old ∨ x ∈ W :=
        hx.imp (fun hp => Finset.mem_union.mpr (Or.inl hp)) id
      have hy' : y ∈ (s.insertBlock Q T hPQ hQW hBudget).old ∨ y ∈ W :=
        hy.imp (fun hp => Finset.mem_union.mpr (Or.inl hp)) id
      exact (ih x y hx' hy').trans
        (s.insertBlock_preserves_live Q T hPQ hQW hBudget x y hx hy)

end Kk
