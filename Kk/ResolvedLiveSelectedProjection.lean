import Kk.ResolvedLiveCoding
import Kk.CanonicalCoverEventLocality
import Mathlib.Tactic

/-!
# Literal fixed-terminal projection during actual resolved cover insertion

English proof: docs/resolved_live_future_normalization_english_20261126.md.
The fixed terminal list may repeat class labels or be empty. The old
graph, full columns, and the image of each support are used literally.
-/

namespace Kk

noncomputable def resolvedTargetAge {n : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (P : Finset Nat) (target : Fin n → Nat) :
    IntegerGraphSupport n ell → Nat :=
  integerGraphAgeCanonical n ell
    (finiteOldColumnRawBound E ell n P (fun p i => E p (target i)))

/-- Full actual reference columns on a fixed terminal list are precisely
the arbitrary sort-map pullback of the active class age. -/
theorem ResolvedLiveStage.targetAge_pullback {d ell n : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (target : Fin n → Nat) (hTarget : ∀ i, target i ∈ W)
    (hell : 0 < ell) (U : IntegerGraphSupport n ell) :
    resolvedTargetAge s.edge ell s.old target U =
      s.oldAge (integerGraphSupportImage (fun i => sort (target i)) U) := by
  let pi := fun i => sort (target i)
  have hCols : ∀ p ∈ s.old, ∀ i, s.edge p (target i) = s.column p (pi i) :=
    fun p hp i => (s.columns p hp (target i) (hTarget i)).1
  unfold resolvedTargetAge
  rw [resolvedOldCanonical_congr_columns (ell := ell) s.edge s.old
    (fun p i => s.column p (pi i)) (fun p i => s.edge p (target i)) hCols]
  exact finiteOldColumnCanonical_reindex s.edge s.old s.column pi hell U

/-- The selected support image lies in the image of the full list, including
when several terminals have the same active class. -/
theorem resolvedSelectedSupport_image_subset {d n ell : Nat}
    (pi : Fin n → Fin d) (U : IntegerGraphSupport n ell) :
    (integerGraphSupportImage pi U).1 ⊆ Finset.univ.image pi := by
  classical
  intro i hi
  change i ∈ U.1.image pi at hi
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩

/-- Omission of the essential support is enough for every actual selected
reference capacity to be unchanged by the cover. No injectivity of the
terminal-to-class map is needed. -/
theorem ResolvedLiveStage.targetAge_neutral_of_omitted_cover {d ell n : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s t : ResolvedLiveStage d ell W sort)
    (target : Fin n → Nat) (hTarget : ∀ i, target i ∈ W)
    (hell : 0 < ell)
    (T : IntegerGraphSupport d ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell) t.oldAge s.oldAge)
    (hChanged : t.oldAge T < s.oldAge T)
    (hMin : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ T.1 → U.1 ≠ T.1 →
      t.oldAge U = s.oldAge U)
    (hOmit : ¬ T.1 ⊆ Finset.univ.image (fun i => sort (target i))) :
    resolvedTargetAge t.edge ell t.old target =
      resolvedTargetAge s.edge ell s.old target := by
  let r := ell - 1 - t.oldAge T
  have hSize := integerGraphAge_cover_changed_support_block_size
    d ell t.oldAge s.oldAge hCover T hChanged
  have hAt := integerGraphAge_cover_changed_support_unit_drop
    d ell t.oldAge s.oldAge hCover T hChanged
  funext U
  rw [t.targetAge_pullback target hTarget hell U,
    s.targetAge_pullback target hTarget hell U]
  apply integerGraphAge_cover_event_preserves_without_full_support
    d ell r hell t.oldAge s.oldAge T _ hCover hSize.2.2 hAt hMin
  intro hSub
  exact hOmit (hSub.trans (resolvedSelectedSupport_image_subset
    (fun i => sort (target i)) U))

/-- Exact neutral age at every partial member set of an actual omitted
cover block. Both endpoint ages are derived from the genuine cover and
the omitted support; the interior uses only antitonicity.
Dummies can be added separately with zero columns. -/
theorem ResolvedLiveStage.insertBlock_omitted_target_all_members {d ell n : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell)
    (target : Fin n → Nat) (hTarget : ∀ i, target i ∈ W)
    (hell : 0 < ell)
    (hCover : AgeCover (IsIntegerGraphAge d ell)
      (s.insertBlock Q T hPQ hQW hBudget).oldAge s.oldAge)
    (hChanged : (s.insertBlock Q T hPQ hQW hBudget).oldAge T < s.oldAge T)
    (hMin : ∀ U : IntegerGraphSupport d ell, U.1 ⊆ T.1 → U.1 ≠ T.1 →
      (s.insertBlock Q T hPQ hQW hBudget).oldAge U = s.oldAge U)
    (hOmit : ¬ T.1 ⊆ Finset.univ.image (fun i => sort (target i)))
    (R : Finset Nat) (hR : R ⊆ Q) :
    resolvedTargetAge (s.insertBlock Q T hPQ hQW hBudget).edge
      ell (s.old ∪ R) target = resolvedTargetAge s.edge ell s.old target := by
  let t := s.insertBlock Q T hPQ hQW hBudget
  have hEnd : resolvedTargetAge t.edge ell t.old target =
      resolvedTargetAge s.edge ell s.old target :=
    s.targetAge_neutral_of_omitted_cover t target hTarget hell T
      hCover hChanged hMin hOmit
  have hStart : resolvedTargetAge t.edge ell s.old target =
      resolvedTargetAge s.edge ell s.old target := by
    unfold resolvedTargetAge
    have hC : ∀ p ∈ s.old, ∀ i, t.edge p (target i) = s.edge p (target i) :=
      fun p hp i => s.insertBlock_preserves_live Q T hPQ hQW hBudget
        p (target i) (Or.inl hp) (Or.inr (hTarget i))
    rw [resolvedOldCanonical_congr_columns (ell := ell) t.edge s.old
      (fun p i => s.edge p (target i)) (fun p i => t.edge p (target i)) hC]
    exact ResolvedLiveStage.oldCanonical_congr_edges (ell := ell)
      s.edge t.edge s.old (fun p i => s.edge p (target i))
      (fun p hp q hq => s.insertBlock_preserves_live Q T hPQ hQW hBudget
        p q (Or.inl hp) (Or.inl hq))
  have hLow : AgeLe (resolvedTargetAge t.edge ell t.old target)
      (resolvedTargetAge t.edge ell (s.old ∪ R) target) := by
    apply resolvedOldCanonical_antitone
    intro p hp
    rcases Finset.mem_union.mp hp with hp' | hp'
    · exact Finset.mem_union.mpr (Or.inl hp')
    · exact Finset.mem_union.mpr (Or.inr (hR hp'))
  have hHigh : AgeLe (resolvedTargetAge t.edge ell (s.old ∪ R) target)
      (resolvedTargetAge t.edge ell s.old target) :=
    resolvedOldCanonical_antitone (ell := ell) t.edge s.old (s.old ∪ R)
      Finset.subset_union_left (fun p i => t.edge p (target i))
  funext U
  apply Nat.le_antisymm
  · rw [← hStart]; exact hHigh U
  · rw [← hEnd]; exact hLow U

/-- No cover member separates two future vertices with identical complete
old columns, even at an intermediate prefix. This supplies the ordinary
no-split certificate, independently of the age-neutrality test. -/
theorem ResolvedLiveStage.insertBlock_no_split {d ell : Nat}
    {W : Set Nat} {sort : Nat → Fin d}
    (s : ResolvedLiveStage d ell W sort)
    (hExact : ResolvedClassExact s.edge s.old W sort)
    (Q : Finset Nat) (T : IntegerGraphSupport d ell)
    (hPQ : Disjoint s.old Q) (hQW : ∀ q ∈ Q, q ∉ W)
    (hBudget : Q.card + s.futureAge T < ell)
    (R : Finset Nat) (q : Nat) (hq : q ∈ Q)
    (v w : Nat) (hv : v ∈ W) (hw : w ∈ W)
    (hOld : ∀ p ∈ s.old ∪ R,
      (s.insertBlock Q T hPQ hQW hBudget).edge p v =
      (s.insertBlock Q T hPQ hQW hBudget).edge p w) :
    (s.insertBlock Q T hPQ hQW hBudget).edge q v =
      (s.insertBlock Q T hPQ hQW hBudget).edge q w := by
  classical
  have hClass : sort v = sort w := by
    apply (hExact v hv w hw).2
    intro p hp
    rw [← s.insertBlock_preserves_live Q T hPQ hQW hBudget p v
      (Or.inl hp) (Or.inr hv),
      ← s.insertBlock_preserves_live Q T hPQ hQW hBudget p w
      (Or.inl hp) (Or.inr hw)]
    exact hOld p (Finset.mem_union.mpr (Or.inl hp))
  have hvQ : v ∉ Q := fun h => hQW v h hv
  have hwQ : w ∉ Q := fun h => hQW w h hw
  change ResolvedLiveStage.blockEdge s.edge Q W sort T.1 q v =
    ResolvedLiveStage.blockEdge s.edge Q W sort T.1 q w
  simp [ResolvedLiveStage.blockEdge, hq, hvQ, hwQ, hv, hw, hClass]

end Kk
