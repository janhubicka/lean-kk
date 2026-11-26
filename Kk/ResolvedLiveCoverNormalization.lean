import Kk.ResolvedLiveFutureAge
import Kk.FiniteCliqueEmbeddingTransport
import Kk.PhysicalCanonicalCoverStage
import Kk.AutomaticAgeCoverChain
import Kk.IntegerAgeCoverUnitDrop
import Kk.TrackFCoverEssentialSupport
import Mathlib.Tactic

/-!
# Actual cover normalization over one live future
English proof: docs/resolved_live_future_normalization_english_20261126.md.
An explicit graph insertion, not left-density in a different graph at
each stage. All old and future vertices persist. The finite cover path
records its actual auxiliary names and minimal supports.
-/

namespace Kk

structure ResolvedLiveStage (d ell : Nat) (W : Set Nat)
    (sort : Nat → Fin d) where
  edge : Nat → Nat → Bool
  old : Finset Nat
  column : Nat → Fin d → Bool
  separated : ∀ p ∈ old, p ∉ W
  columns : ResolvedLiveColumns edge old W sort column
  free : ResolvedLiveFree edge ell old W
  sym : ∀ x y, edge x y = edge y x
  loops : ∀ x, edge x x = false

namespace ResolvedLiveStage

variable {d ell : Nat} {W : Set Nat} {sort : Nat → Fin d}

noncomputable def oldAge (s : ResolvedLiveStage d ell W sort) :
    IntegerGraphSupport d ell → Nat :=
  integerGraphAgeCanonical d ell (finiteOldColumnRawBound s.edge ell d s.old s.column)

noncomputable def futureAge (s : ResolvedLiveStage d ell W sort) :
    IntegerGraphSupport d ell → Nat :=
  resolvedActualAge s.edge ell W sort

theorem future_le_old (s : ResolvedLiveStage d ell W sort) :
    AgeLe s.futureAge s.oldAge :=
  resolvedActualAge_le_oldCanonical s.edge s.old W sort s.column
    s.separated s.columns s.free

/-- Edge table of an actual auxiliary clique on names fresh for the old
prefix and the entire (possibly infinite) live future. -/
noncomputable def blockEdge (E : Nat → Nat → Bool) (Q : Finset Nat)
    (W : Set Nat) (sort : Nat → Fin d) (T : Finset (Fin d))
    (x y : Nat) : Bool := by
  classical
  exact if x ∈ Q then
    if y ∈ Q then decide (x ≠ y) else decide (y ∈ W ∧ sort y ∈ T)
  else if y ∈ Q then decide (x ∈ W ∧ sort x ∈ T) else E x y

theorem blockEdge_off (E : Nat → Nat → Bool) (Q : Finset Nat)
    (T : Finset (Fin d)) {x y : Nat} (hx : x ∉ Q) (hy : y ∉ Q) :
    blockEdge E Q W sort T x y = E x y := by
  classical
  simp [blockEdge, hx, hy]

/-- Fresh block safety in the entire live union, not just a finite sample. -/
theorem blockEdge_live_free (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell) :
    ResolvedLiveFree (blockEdge s.edge Q W sort T.1) ell (s.old ∪ Q) W := by
  classical
  intro C hC hc
  by_cases hHit : ∃ x ∈ C, x ∈ Q
  · obtain ⟨x, hxC, hxQ⟩ := hHit
    let R := C \ Q
    have hR : ∀ y ∈ R, y ∈ W ∧ sort y ∈ T.1 := by
      intro y hy
      obtain ⟨hyC, hyQ⟩ := Finset.mem_sdiff.mp hy
      have hxy : x ≠ y := by
        intro h
        exact hyQ (h ▸ hxQ)
      have hEdge := hc x hxC y hyC hxy
      simpa [blockEdge, hxQ, hyQ] using hEdge
    have hRc : IsDirectedCliqueOn s.edge R := by
      intro a ha b hb hab
      obtain ⟨haC, haQ⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hbC, hbQ⟩ := Finset.mem_sdiff.mp hb
      simpa [blockEdge, haQ, hbQ] using hc a haC b hbC hab
    have hSmall : R.card < ell :=
      s.free R (fun y hy => Or.inr (hR y hy).1) hRc
    have hBound := resolvedActualAge_count_le s.edge W sort R hSmall
      (fun y hy => (hR y hy).1) hRc T
    have hFilter : R.filter (fun v => sort v ∈ T.1) = R := by
      ext y
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun hy => ⟨hy, (hR y hy).2⟩⟩
    rw [hFilter] at hBound
    have hSub : C ⊆ (C ∩ Q) ∪ R := by
      intro y hy
      by_cases hyQ : y ∈ Q
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hy,hyQ⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hy,hyQ⟩))
    have hCard := Finset.card_le_card hSub
    have hUnion := Finset.card_union_le (C ∩ Q) R
    have hInside : (C ∩ Q).card ≤ Q.card :=
      Finset.card_le_card Finset.inter_subset_right
    change Q.card + resolvedActualAge s.edge ell W sort T < ell at hBudget
    omega
  · have hNo : ∀ x ∈ C, x ∉ Q := fun x hx hq => hHit ⟨x,hx,hq⟩
    apply s.free C
    · intro x hx
      rcases hC x hx with hp | hw
      · rcases Finset.mem_union.mp hp with hp' | hq
        · exact Or.inl hp'
        · exact False.elim (hNo x hx hq)
      · exact Or.inr hw
    · intro x hx y hy hxy
      simpa [blockEdge, hNo x hx, hNo y hy] using hc x hx y hy hxy

noncomputable def insertBlock (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell) :
    ResolvedLiveStage d ell W sort := by
  classical
  refine {
    edge := blockEdge s.edge Q W sort T.1
    old := s.old ∪ Q
    column := supportBlockOldColumn Q T.1 s.column
    separated := ?_
    columns := ?_
    free := blockEdge_live_free s Q T hPQ hQW hBudget
    sym := ?_
    loops := ?_ }
  · intro p hp
    rcases Finset.mem_union.mp hp with hp' | hq
    · exact s.separated p hp'
    · exact hQW p hq
  · intro p hp v hv
    have hvQ : v ∉ Q := fun h => hQW v h hv
    rcases Finset.mem_union.mp hp with hp' | hpQ
    · have hpQ : p ∉ Q := fun h => (Finset.disjoint_left.mp hPQ) hp' h
      simpa [blockEdge, supportBlockOldColumn, hpQ, hvQ] using s.columns p hp' v hv
    · simp [blockEdge, supportBlockOldColumn, hpQ, hvQ, hv]
  · intro x y
    by_cases hx : x ∈ Q <;> by_cases hy : y ∈ Q <;>
      simp [blockEdge, hx, hy, s.sym, ne_comm]
  · intro x
    by_cases hx : x ∈ Q <;> simp [blockEdge, hx, s.loops]

theorem insertBlock_preserves_live (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell)
    (x y : Nat) (hx : x ∈ s.old ∨ x ∈ W) (hy : y ∈ s.old ∨ y ∈ W) :
    (s.insertBlock Q T hPQ hQW hBudget).edge x y = s.edge x y := by
  have hNo : ∀ v, v ∈ s.old ∨ v ∈ W → v ∉ Q := by
    intro v hv hq
    rcases hv with hp | hw
    · exact (Finset.disjoint_left.mp hPQ) hp hq
    · exact hQW v hq hw
  exact blockEdge_off s.edge Q T.1 (hNo x hx) (hNo y hy)

theorem insertBlock_futureAge (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell) :
    (s.insertBlock Q T hPQ hQW hBudget).futureAge = s.futureAge := by
  apply resolvedActualAge_congr
  intro x hx y hy
  exact insertBlock_preserves_live s Q T hPQ hQW hBudget x y (Or.inr hx) (Or.inr hy)

private theorem capacity_congr_on (E E' : Nat → Nat → Bool) (P : Finset Nat)
    (hEq : ∀ x ∈ P, ∀ y ∈ P, E' x y = E x y) :
    finiteDirectedCliqueCapacity E' P = finiteDirectedCliqueCapacity E P := by
  have h := finiteDirectedCliqueCapacity_induced_image_eq E E' P (fun x => x)
    (by intro x _hx y _hy h; exact h)
    (fun x hx y hy _hxy => (hEq x hx y hy).symm)
  simpa using h

theorem oldCanonical_congr_edges (E E' : Nat → Nat → Bool)
    (P : Finset Nat) (c : Nat → Fin d → Bool)
    (hEq : ∀ x ∈ P, ∀ y ∈ P, E' x y = E x y) :
    integerGraphAgeCanonical d ell (finiteOldColumnRawBound E' ell d P c) =
      integerGraphAgeCanonical d ell (finiteOldColumnRawBound E ell d P c) := by
  classical
  have hRaw : finiteOldColumnRawBound E' ell d P c =
      finiteOldColumnRawBound E ell d P c := by
    funext T
    unfold finiteOldColumnRawBound
    have hCap := capacity_congr_on E E' (oldSupportCommonNeighbourPool P c T.1)
      (fun x hx y hy => hEq x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    rw [hCap]
  rw [hRaw]

/-- Actual graph insertion realizes the complete prescribed cover. -/
theorem insertBlock_cover_age (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell)
    (lower upper : IntegerGraphSupport d ell → Nat)
    (hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
    (hUpper : s.oldAge = upper)
    (hEll : ell = lower T + Q.card + 1)
    (hAt : upper T = lower T + 1) :
    (s.insertBlock Q T hPQ hQW hBudget).oldAge = lower := by
  classical
  let t := s.insertBlock Q T hPQ hQW hBudget
  have hPrior : integerGraphAgeCanonical d ell
      (finiteOldColumnRawBound t.edge ell d s.old s.column) = upper :=
    (oldCanonical_congr_edges (ell := ell) s.edge t.edge s.old s.column
      (fun x hx y hy => insertBlock_preserves_live s Q T hPQ hQW hBudget
        x y (Or.inl hx) (Or.inl hy))).trans hUpper
  have hZero : ∀ p ∈ s.old, ∀ q ∈ Q, t.edge p q = false := by
    intro p hp q hq
    have hpQ : p ∉ Q := fun h => (Finset.disjoint_left.mp hPQ) hp h
    change blockEdge s.edge Q W sort T.1 p q = false
    simp [blockEdge, hpQ, hq, s.separated p hp]
  have hClique : IsDirectedCliqueOn t.edge Q := by
    intro x hx y hy hxy
    change blockEdge s.edge Q W sort T.1 x y = true
    simp [blockEdge, hx, hy, hxy]
  have hCap := isolatedReservedClique_capacity_eq_card t.edge Q hClique
  have hAge := isolatedSupportCanonicalAge_cover_step t.edge ell d Q.card
    s.old Q hPQ hZero s.column T lower upper hCover hEll hAt hPrior hCap.le
  change integerGraphAgeCanonical d ell
    (finiteOldColumnRawBound t.edge ell d (s.old ∪ Q)
      (supportBlockOldColumn Q T.1 s.column)) = lower
  rw [hAge, hCap, if_neg (lt_irrefl _)]

end ResolvedLiveStage

/-- Actual insertion trace, with all fresh names and the essential support
stored at each step. States refer to the SAME live future set. -/
inductive ResolvedLiveCoverPath {d ell : Nat} (W : Set Nat) (sort : Nat → Fin d) :
    ResolvedLiveStage d ell W sort → ResolvedLiveStage d ell W sort → Prop where
  | stop (s : ResolvedLiveStage d ell W sort) :
      ResolvedLiveCoverPath W sort s s
  | advance (s : ResolvedLiveStage d ell W sort)
      (Q : Finset Nat) (T : IntegerGraphSupport d ell)
      (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
      (hBudget : Q.card + s.futureAge T < ell)
      (hCover : AgeCover (IsIntegerGraphAge d ell)
        (s.insertBlock Q T hPQ hQW hBudget).oldAge s.oldAge)
      (hChanged : (s.insertBlock Q T hPQ hQW hBudget).oldAge T < s.oldAge T)
      (hMinimal : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ T.1 → U.1 ≠ T.1 →
        (s.insertBlock Q T hPQ hQW hBudget).oldAge U = s.oldAge U)
      (hSize : ell = (s.insertBlock Q T hPQ hQW hBudget).oldAge T + Q.card + 1)
      {finish : ResolvedLiveStage d ell W sort}
      (tail : ResolvedLiveCoverPath W sort (s.insertBlock Q T hPQ hQW hBudget) finish) :
      ResolvedLiveCoverPath W sort s finish

/-- Sufficient spare names are available when the original V is
represented on even naturals. This is independent of any Henson density. -/
theorem resolvedFreshOdd (W : Set Nat) (hEven : ∀ v ∈ W, v % 2 = 0)
    (P : Finset Nat) (r : Nat) :
    ∃ Q : Finset Nat, Q.card = r ∧ Disjoint P Q ∧ ∀ q ∈ Q, q ∉ W := by
  classical
  let f : Nat → Nat := fun i => 2 * (P.sup (fun p => p) + i) + 1
  have hInj : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    omega
  let Q := (Finset.range r).image f
  refine ⟨Q, ?_, ?_, ?_⟩
  · change ((Finset.range r).image f).card = r
    rw [Finset.card_image_of_injective _ hInj, Finset.card_range]
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hq
    have hMax := Finset.le_sup (f := fun p : Nat => p) hp
    dsimp [f] at he
    omega
  · intro q hq hw
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hq
    have h := hEven q hw
    dsimp [f] at he
    omega

private theorem resolvedCoverChain_end_le_start
    {d ell : Nat} {U L : IntegerGraphSupport d ell → Nat}
    (path : AgeCoverChain (IsIntegerGraphAge d ell) U L) :
    AgeLe L U := by
  induction path with
  | refl A => exact fun _ => le_rfl
  | step hCover tail ih => exact fun T => (ih T).trans (hCover.le T)

/-- Build an actual finite saturated cover path down to the maximum
clique capacities of the same original live future. It constructs all
fresh auxiliary blocks, proves safety on the whole live union, and
preserves every edge on the old-plus-future starting domain. -/
theorem resolvedLive_normalizes_actual_future_by_covers {d ell : Nat}
    (W : Set Nat) (sort : Nat → Fin d)
    (s : ResolvedLiveStage d ell W sort) (hell : 1 < ell)
    (hOccupied : ∀ i, ∃ v ∈ W, sort v = i)
    (hFresh : ∀ (P : Finset Nat) (r : Nat),
      ∃ Q : Finset Nat, Q.card = r ∧ Disjoint P Q ∧ ∀ q ∈ Q, q ∉ W) :
    ∃ t : ResolvedLiveStage d ell W sort,
      ResolvedLiveCoverPath W sort s t ∧ t.oldAge = s.futureAge ∧
      t.futureAge = s.futureAge ∧ s.old ⊆ t.old ∧
      (∀ x y : Nat, (x ∈ s.old ∨ x ∈ W) → (y ∈ s.old ∨ y ∈ W) →
        t.edge x y = s.edge x y) := by
  classical
  let target := s.futureAge
  have hTarget : IsIntegerGraphAge d ell target :=
    resolvedActualAge_is_age s.edge W sort hell hOccupied
  have hUpper : IsIntegerGraphAge d ell s.oldAge := by
    apply integerGraphAgeCanonical_is_age d ell _ target hTarget
    intro T
    exact (s.future_le_old T).trans (integerGraphAgeCanonical_le_raw d ell _ T)
  have hChain := integerGraphAge_exists_saturated_chain d ell target s.oldAge
    hTarget hUpper s.future_le_old
  have hBuild : ∀ {U L : IntegerGraphSupport d ell → Nat},
      AgeCoverChain (IsIntegerGraphAge d ell) U L →
      ∀ a : ResolvedLiveStage d ell W sort, a.oldAge = U →
        a.futureAge = target → AgeLe target L →
        ∃ z : ResolvedLiveStage d ell W sort,
          ResolvedLiveCoverPath W sort a z ∧ z.oldAge = L ∧
          z.futureAge = target ∧ a.old ⊆ z.old ∧
          (∀ x y : Nat, (x ∈ a.old ∨ x ∈ W) → (y ∈ a.old ∨ y ∈ W) →
            z.edge x y = a.edge x y) := by
    intro U L path
    induction path with
    | refl A =>
        intro a hAge hFuture _
        exact ⟨a, .stop a, hAge, hFuture, Finset.Subset.refl _, (by intros; rfl)⟩
    | @step A M L hCover tail ih =>
        intro a hAge hFuture hTargetL
        obtain ⟨T, hChanged, hMin⟩ :=
          trackFCover_exists_minimal_changed d ell M A hCover
        let r := ell - 1 - M T
        have hArith := integerGraphAge_cover_changed_support_block_size d ell M A hCover T hChanged
        have hAt := integerGraphAge_cover_changed_support_unit_drop d ell M A hCover T hChanged
        have hLM : AgeLe L M := resolvedCoverChain_end_le_start tail
        obtain ⟨Q,hSize,hPQ,hQW⟩ := hFresh a.old r
        have hBudget : Q.card + a.futureAge T < ell := by
          have hBound : target T ≤ M T := (hTargetL T).trans (hLM T)
          rw [hSize, hFuture]
          have hEll : ell = M T + r + 1 := hArith.2.2
          omega
        let mid := a.insertBlock Q T hPQ hQW hBudget
        have hEll : ell = M T + Q.card + 1 := by
          rw [hSize]
          exact hArith.2.2
        have hMid : mid.oldAge = M :=
          a.insertBlock_cover_age Q T hPQ hQW hBudget M A hCover hAge hEll hAt
        have hMidFuture : mid.futureAge = target :=
          (a.insertBlock_futureAge Q T hPQ hQW hBudget).trans hFuture
        obtain ⟨z,hTail,hZAge,hZFuture,hOld,hKeep⟩ :=
          ih mid hMid hMidFuture hTargetL
        have hSub : a.old ⊆ mid.old := Finset.subset_union_left
        have hC : AgeCover (IsIntegerGraphAge d ell) mid.oldAge a.oldAge := by
          rw [hMid,hAge]; exact hCover
        have hD : mid.oldAge T < a.oldAge T := by
          rw [hMid,hAge]; exact hChanged
        have hMin' : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ T.1 → U.1 ≠ T.1 →
            mid.oldAge U = a.oldAge U := by
          rw [hMid,hAge]; exact hMin
        have hSize' : ell = mid.oldAge T + Q.card + 1 := by
          rw [hMid]; exact hEll
        refine ⟨z, .advance a Q T hPQ hQW hBudget hC hD hMin' hSize' hTail,
          hZAge,hZFuture,hSub.trans hOld,?_⟩
        intro x y hx hy
        have hx' : x ∈ mid.old ∨ x ∈ W := hx.imp (fun hp => hSub hp) id
        have hy' : y ∈ mid.old ∨ y ∈ W := hy.imp (fun hp => hSub hp) id
        exact (hKeep x y hx' hy').trans
          (a.insertBlock_preserves_live Q T hPQ hQW hBudget x y hx hy)
  exact hBuild hChain s rfl rfl (fun _ => le_rfl)

end Kk
