import Kk.IntegerAgeCoverRestriction
import Kk.ResolvedFairCriticalRetention
import Kk.ResolvedNeutralCap
import Kk.IsolatedSupportCanonicalAge
import Mathlib.Tactic

/-!
# Actual event-level projection to selected occupied classes

Exact old-column labels are now retained in every cover certificate.
No-split therefore follows for every member of the actual cover block.
For cover projection one representative of each occupied selected class
is used; repeated terminal labels are NOT incorrectly treated as an
injective restriction.
-/

namespace Kk
open SuccessorTree.V10

theorem resolvedTargetAge_congr_on {n ell : Nat}
    (E F : Nat → Nat → Bool) (P : Finset Nat) (target : Fin n → Nat)
    (hEdge : ∀ x ∈ P, ∀ y ∈ P, E x y = F x y)
    (hCol : ∀ x ∈ P, ∀ i, E x (target i) = F x (target i)) :
    resolvedTargetAge E ell P target = resolvedTargetAge F ell P target := by
  unfold resolvedTargetAge
  have h := integerGraphAgeCanonical_induced_image_eq F E ell n P
    (fun x i => F x (target i)) (fun x i => E x (target i)) id
    Function.injective_id (fun x hx y hy _ => hEdge x hx y hy) hCol
  simpa using h

theorem ResolvedEventCertificate.cover_no_split {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hKind : e.kind = .cover) (q : Nat) (hq : q ∈ e.block)
    (v w : Nat) (hv : v ∈ W) (hw : w ∈ W)
    (hOld : ∀ p ∈ e.preOld, e.edge p v = e.edge p w) :
    e.edge q v = e.edge q w := by
  cases h with
  | marker => simp at hKind
  | code => simp at hKind
  | cover s Q T hPQ hQW hBudget hCover hChanged hMinimal hSize hExact =>
      exact s.insertBlock_no_split hExact Q T hPQ hQW hBudget ∅ q
        (by simpa using hq) v w hv hw (by simpa using hOld)

/-- A marker's positive terminals lie in exactly one old column class.
Thus one marker cannot create two different selected splits. -/
theorem ResolvedEventCertificate.marker_positive_same_old {W : Set Nat} {r : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hKind : e.kind = .marker) (q : Nat) (hq : q ∈ e.block)
    (v w : Nat) (hv : v ∈ W) (hw : w ∈ W)
    (hV : e.edge q v = true) (hW : e.edge q w = true) :
    ∀ p ∈ e.preOld, e.edge p v = e.edge p w := by
  cases h with
  | cover => simp at hKind
  | code => simp at hKind
  | marker s sort f hEven hSafe hExact i hMixed R hR hNot =>
      have hqEq : q = resolvedMarkerName s.old i := by simpa using hq
      subst q
      obtain ⟨a,ha,b,hb,_hAB,_hPos,_hNeg,hClass⟩ :=
        s.refineBatch_single_split sort f hEven hSafe hExact i hMixed R hR hNot
      have hvOld := ((hClass v hv).mp hV).1
      have hwOld := ((hClass w hw).mp hW).1
      intro p hp
      exact (hvOld p hp).trans (hwOld p hp).symm

/-- Project a real cover onto a list of representatives of distinct
old-column classes. The complete old and new ages are the actual
event tables, not merely raw constraints or declared profiles. -/
theorem ResolvedEventCertificate.cover_targetAge_cover_or_eq {W : Set Nat} {r n : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hKind : e.kind = .cover) (target : Fin n → Nat)
    (hTarget : ∀ i, target i ∈ W)
    (hDistinct : ∀ i j : Fin n, i ≠ j →
      ∃ p ∈ e.preOld, e.edge p (target i) ≠ e.edge p (target j)) :
    resolvedTargetAge e.edge 4 e.postOld target =
      resolvedTargetAge e.edge 4 e.preOld target ∨
    AgeCover (IsIntegerGraphAge n 4)
      (resolvedTargetAge e.edge 4 e.postOld target)
      (resolvedTargetAge e.edge 4 e.preOld target) := by
  cases h with
  | marker => simp at hKind
  | code => simp at hKind
  | cover s Q T hPQ hQW hBudget hCover hChanged hMinimal hSize hExact =>
      let t := s.insertBlock Q T hPQ hQW hBudget
      let pi := fun i => sort (target i)
      have hKeep := s.insertBlock_preserves_live Q T hPQ hQW hBudget
      have hi : Function.Injective pi := by
        intro i j hEq
        by_contra hNe
        obtain ⟨p,hp,hBad⟩ := hDistinct i j hNe
        apply hBad
        exact (hKeep p (target i) (Or.inl hp) (Or.inr (hTarget i))).trans
          (((hExact (target i) (hTarget i) (target j) (hTarget j)).mp hEq p hp).trans
            (hKeep p (target j) (Or.inl hp) (Or.inr (hTarget j))).symm)
      have hOldEq : resolvedTargetAge t.edge 4 s.old target =
          resolvedTargetAge s.edge 4 s.old target :=
        resolvedTargetAge_congr_on t.edge s.edge s.old target
          (fun x hx y hy => hKeep x y (Or.inl hx) (Or.inl hy))
          (fun x hx i => hKeep x (target i) (Or.inl hx) (Or.inr (hTarget i)))
      have hOld : resolvedTargetAge t.edge 4 s.old target =
          (fun U => s.oldAge (integerGraphSupportImage pi U)) :=
        hOldEq.trans (funext (s.targetAge_pullback target hTarget (by decide)))
      have hNew : resolvedTargetAge t.edge 4 t.old target =
          (fun U => t.oldAge (integerGraphSupportImage pi U)) :=
        funext (t.targetAge_pullback target hTarget (by decide))
      have hPost : s.old ∪ Q.sort.toFinset = t.old := by
        simp [t,ResolvedLiveStage.insertBlock]
      change resolvedTargetAge t.edge 4 (s.old ∪ Q.sort.toFinset) target =
          resolvedTargetAge t.edge 4 s.old target ∨ _
      rw [hPost,hOld,hNew]
      exact integerGraphAge_cover_injective_pullback pi hi (by decide) _ _ hCover

/-- Equal endpoint ages at an event imply equality at every intermediate
old pool. A partially inserted omitted block has no hidden age change. -/
theorem resolvedTargetAge_neutral_between {n ell : Nat}
    (E : Nat → Nat → Bool) (P R Q : Finset Nat) (target : Fin n → Nat)
    (hPR : P ⊆ R) (hRQ : R ⊆ Q)
    (hEq : resolvedTargetAge E ell Q target = resolvedTargetAge E ell P target) :
    resolvedTargetAge E ell R target = resolvedTargetAge E ell P target := by
  have h1 := resolvedOldCanonical_antitone (ell := ell) E P R hPR
    (fun p i => E p (target i))
  have h2 := resolvedOldCanonical_antitone (ell := ell) E R Q hRQ
    (fun p i => E p (target i))
  funext U
  apply Nat.le_antisymm (h1 U)
  rw [← hEq]
  exact h2 U

/-- A noncoding event is an isolated clique with a uniform selected
column. Its effect on all canonical witnesses is exactly one support
clipping by the actual block size. This works for both markers and
covers, not just ideal single-coordinate raw updates. -/
theorem ResolvedEventCertificate.aux_targetAge_clip {W : Set Nat} {r n : Nat}
    {e : ResolvedEvent} (h : ResolvedEventCertificate W r e)
    (hAux : e.kind ≠ .code) (target : Fin n → Nat)
    (T : IntegerGraphSupport n 4)
    (hLink : ∀ q ∈ e.block, ∀ i, e.edge q (target i) = decide (i ∈ T.1)) :
    resolvedTargetAge e.edge 4 e.postOld target =
      integerGraphAgeCanonical n 4 (rawCliqueBlockBound 4 e.block.length
        (resolvedTargetAge e.edge 4 e.preOld target) T) := by
  classical
  let Q := e.block.toFinset
  let P := e.preOld
  let c := fun p i => e.edge p (target i)
  have hDisj : Disjoint P Q := h.block_fresh
  have hZero : ∀ p ∈ P, ∀ q ∈ Q, e.edge p q = false :=
    fun p hp q hq => (h.auxiliary_old_zero hAux p q hp (List.mem_toFinset.mp hq)).1
  have hCard : Q.card = e.block.length := List.toFinset_card_of_nodup h.block_nodup
  have hCap : finiteDirectedCliqueCapacity e.edge Q = e.block.length := by
    rw [← hCard]
    apply Nat.le_antisymm
    · obtain ⟨C,hC,_hClique,hSize⟩ := finiteDirectedCliqueCapacity_attained e.edge Q
      rw [← hSize]
      exact Finset.card_le_card hC
    · exact directedClique_card_le_capacity e.edge Q Q (Finset.Subset.refl _) h.block_clique
  have hCols : ∀ p ∈ P ∪ Q, ∀ i,
      c p i = supportBlockOldColumn Q T.1 c p i := by
    intro p _ i
    by_cases hq : p ∈ Q
    · rw [supportBlockOldColumn_on_reserved _ _ _ _ _ hq]
      exact hLink p (List.mem_toFinset.mp hq) i
    · rw [supportBlockOldColumn_off_reserved _ _ _ _ _ hq]
  unfold resolvedTargetAge
  change integerGraphAgeCanonical n 4 (finiteOldColumnRawBound e.edge 4 n (P ∪ Q) c) = _
  rw [resolvedOldCanonical_congr_columns (ell := 4) e.edge (P ∪ Q)
    (supportBlockOldColumn Q T.1 c) c hCols]
  rw [isolatedSupportCanonicalAge_eq_ideal e.edge 4 n P Q hDisj hZero c T,
    hCap, integerGraphAgeCanonical_idealBlock_congr]

/-- Saturation and the actual singleton coded class force capacity
one. The proof uses a real clique attaining the future age. -/
theorem ResolvedLiveStage.saturatedCode_singleton_capacity {d : Nat}
    {W : Set Nat} {sort : Nat → Fin d} (s : ResolvedLiveStage d 4 W sort)
    (r : Nat) (hr : r ∈ W)
    (hSat : s.oldAge = s.futureAge)
    (hSingleton : ∀ v ∈ W, sort v = sort r → v = r)
    (T : IntegerGraphSupport d 4) (hT : T.1 = {sort r}) :
    s.oldAge T = 1 := by
  classical
  rw [hSat]
  change resolvedActualAge s.edge 4 W sort T = 1
  obtain ⟨C,hSmall,hMem,hClique,hCard⟩ :=
    resolvedActualAge_attained_supported s.edge W sort (by decide) T
  apply Nat.le_antisymm
  · have hSub : C ⊆ ({r} : Finset Nat) := by
      intro x hx
      apply Finset.mem_singleton.mpr
      apply hSingleton x (hMem x hx).1
      have h := (hMem x hx).2
      rw [hT] at h
      exact Finset.mem_singleton.mp h
    rw [← hCard]
    simpa using Finset.card_le_card hSub
  · have hSingle : IsDirectedCliqueOn s.edge ({r} : Finset Nat) := by
      intro x hx y hy hxy
      exact False.elim (hxy ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm))
    have hCount := resolvedActualAge_count_le s.edge W sort ({r} : Finset Nat)
      (by decide) (by intro x hx; exact (Finset.mem_singleton.mp hx).symm ▸ hr) hSingle T
    simpa [hT] using hCount

/-- The original selected-only moving front already satisfies both
local tests at any real coding coordinate, without the extra cap. -/
theorem resolvedNeutralCapFront_code_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (n m : Nat) :
    let keep := resolvedFairSelectedKeep s0 S auxKeep
    let c := resolvedFairOriginalAddress s0 m
    (∀ i j : Fin (resolvedNeutralCapFrontSize s0 keep n c),
      (∀ p < c, oneGapEdge (resolvedFairEventEdge s0) p (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) p (resolvedNeutralCapFront s0 keep n c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c j)) ∧
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
      (resolvedNeutralCapFront s0 keep n c) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
      (resolvedNeutralCapFront s0 keep n c) := by
  dsimp only
  let keep := resolvedFairSelectedKeep s0 S auxKeep
  let N := resolvedNeutralCapSize s0 n
  let V := resolvedNeutralCapOldPool s0 keep n
  let c := resolvedFairOriginalAddress s0 m
  let target := resolvedFairSelectedFrontIndex s0 hEmpty S auxKeep N V c
  have hLater : ∀ i, m < target i :=
    resolvedFairSelectedFrontIndex_later s0 hEmpty S auxKeep N V m
  have hAddr : resolvedNeutralCapFront s0 keep n c =
      fun i => resolvedFairOriginalAddress s0 (target i) := by
    funext i
    exact resolvedFairSelectedFrontIndex_address s0 hEmpty S auxKeep N V c i
  constructor
  · intro i j hOld
    rw [hAddr] at hOld ⊢
    exact resolvedFairOriginalCoding_no_split s0 hEmpty m (target i) (target j)
      (hLater i) (hLater j) hOld
  · rw [hAddr]
    exact resolvedFairOriginalCoding_targetAge_neutral s0 hEmpty m target hLater

end Kk
