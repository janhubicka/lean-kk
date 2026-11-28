import Kk.ResolvedEventProjection
import Kk.OneGapInverseSource
import Mathlib.Tactic

/-!
# Selected-only event retention and the actual neutral-cap envelope

The canonical future list is the increasing enumeration of the
requested original indices whose coding event is strictly later.
An auxiliary event is omitted exactly when its entire projected age
is unchanged and it separates no two previously equal selected
columns. These tests use the ACTUAL chronological graph.

The final theorem derives the local envelope hypotheses from these
flags, then constructs actual common preimages for all selected
G+ vertices. Neither the extra real terminal used by the coarse bound
nor a fixed-terminal rank budget occurs in this construction.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

noncomputable def resolvedDiaryFuture
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (k : Nat) : Finset Nat :=
  S.filter (fun i => k < resolvedFairCodingEvent s0 i)

noncomputable def resolvedDiaryTarget
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (k : Nat) :
    Fin (resolvedDiaryFuture s0 S k).card → Nat :=
  fun i => resolvedFairEventCodePosition s0
    ((resolvedDiaryFuture s0 S k).orderEmbOfFin rfl i)

def resolvedDiaryAuxNeutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (k : Nat) : Prop :=
  resolvedTargetAge (resolvedFairEventEdge s0) 4
    (Finset.range (resolvedFairEventBoundary s0 (k+1))) (resolvedDiaryTarget s0 S k) =
  resolvedTargetAge (resolvedFairEventEdge s0) 4
    (Finset.range (resolvedFairEventBoundary s0 k)) (resolvedDiaryTarget s0 S k) ∧
  ∀ i ∈ resolvedDiaryFuture s0 S k, ∀ j ∈ resolvedDiaryFuture s0 S k,
    (∀ q < resolvedFairEventBoundary s0 k,
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 i) =
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 j)) →
    ∀ q, resolvedFairEventBoundary s0 k ≤ q →
      q < resolvedFairEventBoundary s0 (k+1) →
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 i) =
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 j)

noncomputable def resolvedDiaryAuxKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0))
    (S : Finset Nat) (k : Nat) : Bool := by
  classical
  exact decide (¬ resolvedDiaryAuxNeutral s0 S k)

noncomputable def resolvedDiaryKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) : Nat → Bool :=
  resolvedFairSelectedKeep s0 S (resolvedDiaryAuxKeep s0 S)

/-- A target-age equality on the complete list transports to an
arbitrary finite sublist, with repeats allowed. -/
theorem resolvedTargetAge_reindex {e d ell : Nat}
    (E : Nat → Nat → Bool) (P : Finset Nat)
    (f : Fin d → Nat) (pi : Fin e → Fin d) (hell : 0 < ell) :
    resolvedTargetAge E ell P (fun i => f (pi i)) =
      (fun U => resolvedTargetAge E ell P f (integerGraphSupportImage pi U)) := by
  funext U
  exact finiteOldColumnCanonical_reindex E P (fun p i => E p (f i)) pi hell U

/-- An actual chronological position lies in exactly its event interval. -/
theorem resolvedFairEventBoundary_bounds
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (p : Nat) :
    resolvedFairEventBoundary s0 (resolvedFairVertexEventIndex s0 p) ≤ p ∧
    p < resolvedFairEventBoundary s0 (resolvedFairVertexEventIndex s0 p + 1) :=
  oneGapBatchIndex_bounds _ (resolvedFairEventBlock_positive s0) p

/-- The old names at the end of an event are precisely the pre-old
names at the next event. This includes the transition between rounds. -/
theorem resolvedFairEvent_postOld_eq_next
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) :
    (resolvedFairEvent s0 k).postOld = (resolvedFairEvent s0 (k+1)).preOld := by
  classical
  ext v
  unfold ResolvedEvent.postOld
  rw [Finset.mem_union, resolvedFairEvent_preOld_iff s0 hEmpty k,
    resolvedFairEvent_preOld_iff s0 hEmpty (k+1), List.mem_toFinset]
  constructor
  · rintro (⟨j,hj,hv⟩ | hv)
    · exact ⟨j,by omega,hv⟩
    · exact ⟨k,by omega,hv⟩
  · rintro ⟨j,hj,hv⟩
    by_cases he : j = k
    · subst j
      exact Or.inr hv
    · exact Or.inl ⟨j,by omega,hv⟩

theorem resolvedFairEventBoundary_pre_image
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) :
    (Finset.range (resolvedFairEventBoundary s0 k)).image
      (resolvedFairEventVertex s0) = (resolvedFairEvent s0 k).preOld := by
  classical
  ext v
  simpa only [Finset.mem_image, Finset.mem_range] using
    resolvedFairEventVertex_prefix s0 hEmpty k v

theorem resolvedFairEventBoundary_post_image
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) :
    (Finset.range (resolvedFairEventBoundary s0 (k+1))).image
      (resolvedFairEventVertex s0) = (resolvedFairEvent s0 k).postOld :=
  (resolvedFairEventBoundary_pre_image s0 hEmpty (k+1)).trans
    (resolvedFairEvent_postOld_eq_next s0 hEmpty k).symm

/-- Every later original belongs to the actual live set of this event. -/
theorem resolvedFairEvent_later_original_live
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k i : Nat)
    (hi : k < resolvedFairCodingEvent s0 i) :
    2*i ∈ resolvedEvenTail (resolvedFairEventLocation s0 k).1 := by
  let size := fun n => (resolvedFairRoundEvents s0 n).length
  have hMono := oneGapBatchIndex_mono size (resolvedFairRoundEvents_positive s0) hi.le
  change (resolvedFairEventLocation s0 k).1 ≤
    (resolvedFairEventLocation s0 (resolvedFairCodingEvent s0 i)).1 at hMono
  rw [resolvedFairCodingEvent_location] at hMono
  change (2*i) % 2 = 0 ∧ 2*(resolvedFairEventLocation s0 k).1 ≤ 2*i
  exact ⟨by omega,by omega⟩

/-- Transport the actual canonical age at any prefix ending inside the
event, including its endpoints, to the corresponding native pool.
The entire old graph and every selected column are transported. -/
theorem resolvedFairEvent_targetAge_transport
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) {d : Nat} (target : Fin d → Nat)
    (hTarget : ∀ i, k < resolvedFairCodingEvent s0 (target i))
    (P : Finset Nat)
    (hP : P ⊆ Finset.range (resolvedFairEventBoundary s0 (k+1))) :
    resolvedTargetAge (resolvedFairEventEdge s0) 4 P
      (fun i => resolvedFairEventCodePosition s0 (target i)) =
    resolvedTargetAge (resolvedFairEvent s0 k).edge 4
      (P.image (resolvedFairEventVertex s0)) (fun i => 2*target i) := by
  have hOld (p : Nat) (hp : p ∈ P) :
      resolvedFairEventVertex s0 p ∈ (resolvedFairEvent s0 k).postOld := by
    rw [← resolvedFairEventBoundary_post_image s0 hEmpty k]
    exact Finset.mem_image.mpr ⟨p,hP hp,rfl⟩
  unfold resolvedTargetAge
  symm
  apply integerGraphAgeCanonical_induced_image_eq
    (resolvedFairEventEdge s0) (resolvedFairEvent s0 k).edge 4 d P
    (fun p i => resolvedFairEventEdge s0 p (resolvedFairEventCodePosition s0 (target i)))
    (fun p i => (resolvedFairEvent s0 k).edge p (2*target i))
    (resolvedFairEventVertex s0) (resolvedFairEventVertex_injective s0 hEmpty)
  · intro x hx y hy _
    exact (resolvedFairEvent_agreement s0 k _ _
      (Or.inl (hOld x hx)) (Or.inl (hOld y hy))).symm
  · intro x hx i
    have h := resolvedFairEvent_agreement s0 k (resolvedFairEventVertex s0 x) (2*target i)
      (Or.inl (hOld x hx))
      (Or.inr (resolvedFairEvent_later_original_live s0 k (target i) (hTarget i)))
    change (resolvedFairEvent s0 k).edge (resolvedFairEventVertex s0 x) (2*target i) =
      resolvedFairEdge s0 (resolvedFairEventVertex s0 x)
        (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 (target i)))
    rw [resolvedFairEventVertex_coded]
    exact h.symm

/-- Native pre/post cover projection is now available at the actual
chronological event boundaries. Distinctness refers to real old columns. -/
theorem resolvedFairEvent_cover_projection
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) (hKind : (resolvedFairEvent s0 k).kind = .cover)
    {d : Nat} (target : Fin d → Nat)
    (hTarget : ∀ i, k < resolvedFairCodingEvent s0 (target i))
    (hDistinct : ∀ i j : Fin d, i ≠ j → ∃ q < resolvedFairEventBoundary s0 k,
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 (target i)) ≠
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 (target j))) :
    let lower := resolvedTargetAge (resolvedFairEventEdge s0) 4
      (Finset.range (resolvedFairEventBoundary s0 (k+1)))
      (fun i => resolvedFairEventCodePosition s0 (target i))
    let upper := resolvedTargetAge (resolvedFairEventEdge s0) 4
      (Finset.range (resolvedFairEventBoundary s0 k))
      (fun i => resolvedFairEventCodePosition s0 (target i))
    lower = upper ∨ AgeCover (IsIntegerGraphAge d 4) lower upper := by
  dsimp only
  have hBound : resolvedFairEventBoundary s0 k ≤ resolvedFairEventBoundary s0 (k+1) :=
    (oneGapBatchBoundary_strictMono _ (resolvedFairEventBlock_positive s0)).monotone
      (Nat.le_succ k)
  have hBefore := resolvedFairEvent_targetAge_transport s0 hEmpty k target hTarget
    (Finset.range (resolvedFairEventBoundary s0 k))
    (by intro q hq; exact Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hBound))
  have hAfter := resolvedFairEvent_targetAge_transport s0 hEmpty k target hTarget
    (Finset.range (resolvedFairEventBoundary s0 (k+1))) (Finset.Subset.refl _)
  rw [resolvedFairEventBoundary_pre_image s0 hEmpty k] at hBefore
  rw [resolvedFairEventBoundary_post_image s0 hEmpty k] at hAfter
  have hLive (i : Fin d) : 2*target i ∈ resolvedEvenTail (resolvedFairEventLocation s0 k).1 :=
    resolvedFairEvent_later_original_live s0 k (target i) (hTarget i)
  have hNative : ∀ i j : Fin d, i ≠ j →
      ∃ q ∈ (resolvedFairEvent s0 k).preOld,
        (resolvedFairEvent s0 k).edge q (2*target i) ≠
        (resolvedFairEvent s0 k).edge q (2*target j) := by
    intro i j hij
    obtain ⟨q,hq,hne⟩ := hDistinct i j hij
    have hqOld := (resolvedFairEventVertex_prefix s0 hEmpty k _).mp ⟨q,hq,rfl⟩
    have hqPost : resolvedFairEventVertex s0 q ∈ (resolvedFairEvent s0 k).postOld :=
      Finset.mem_union.mpr (Or.inl hqOld)
    refine ⟨resolvedFairEventVertex s0 q,hqOld,?_⟩
    intro he
    apply hne
    change resolvedFairEdge s0 (resolvedFairEventVertex s0 q)
      (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 (target i))) =
      resolvedFairEdge s0 (resolvedFairEventVertex s0 q)
      (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 (target j)))
    rw [resolvedFairEventVertex_coded,resolvedFairEventVertex_coded]
    exact (resolvedFairEvent_agreement s0 k _ _ (Or.inl hqPost) (Or.inr (hLive i))).trans
      (he.trans (resolvedFairEvent_agreement s0 k _ _ (Or.inl hqPost) (Or.inr (hLive j))).symm)
  rw [hBefore,hAfter]
  exact (resolvedFairEvent_certificate s0 k).cover_targetAge_cover_or_eq
    hKind (fun i => 2*target i) hLive hNative

/-- No split in any member of an actual cover block, transported from
the exact pre-old class certificate. -/
theorem resolvedFairEvent_cover_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (p v w : Nat)
    (hKind : (resolvedFairEvent s0 (resolvedFairVertexEventIndex s0 p)).kind = .cover)
    (hv : resolvedFairVertexEventIndex s0 p < resolvedFairCodingEvent s0 v)
    (hw : resolvedFairVertexEventIndex s0 p < resolvedFairCodingEvent s0 w)
    (hOld : ∀ q < resolvedFairEventBoundary s0 (resolvedFairVertexEventIndex s0 p),
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 v) =
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 w)) :
    resolvedFairEventEdge s0 p (resolvedFairEventCodePosition s0 v) =
      resolvedFairEventEdge s0 p (resolvedFairEventCodePosition s0 w) := by
  let k := resolvedFairVertexEventIndex s0 p
  have hV := resolvedFairEvent_later_original_live s0 k v hv
  have hW := resolvedFairEvent_later_original_live s0 k w hw
  have hCol (q : Nat) (hq : q ∈ (resolvedFairEvent s0 k).postOld) (i : Nat)
      (hi : k < resolvedFairCodingEvent s0 i) :
      resolvedFairEdge s0 q (2*i) = (resolvedFairEvent s0 k).edge q (2*i) :=
    resolvedFairEvent_agreement s0 k _ _ (Or.inl hq)
      (Or.inr (resolvedFairEvent_later_original_live s0 k i hi))
  have hNative : ∀ q ∈ (resolvedFairEvent s0 k).preOld,
      (resolvedFairEvent s0 k).edge q (2*v) =
      (resolvedFairEvent s0 k).edge q (2*w) := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := (resolvedFairEventVertex_prefix s0 hEmpty k q).mpr hq
    have hPost : resolvedFairEventVertex s0 j ∈ (resolvedFairEvent s0 k).postOld :=
      Finset.mem_union.mpr (Or.inl hq)
    have hb := hOld j hj
    change resolvedFairEdge s0 (resolvedFairEventVertex s0 j)
        (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 v)) =
      resolvedFairEdge s0 (resolvedFairEventVertex s0 j)
        (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 w)) at hb
    rw [resolvedFairEventVertex_coded,resolvedFairEventVertex_coded] at hb
    exact (hCol _ hPost v hv).symm.trans (hb.trans (hCol _ hPost w hw))
  have hq := resolvedFairEventVertex_mem_block s0 p
  have hPost : resolvedFairEventVertex s0 p ∈ (resolvedFairEvent s0 k).postOld :=
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hq))
  have he := (resolvedFairEvent_certificate s0 k).cover_no_split
    hKind _ hq (2*v) (2*w) hV hW hNative
  change resolvedFairEdge s0 (resolvedFairEventVertex s0 p)
      (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 v)) =
    resolvedFairEdge s0 (resolvedFairEventVertex s0 p)
      (resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 w))
  rw [resolvedFairEventVertex_coded,resolvedFairEventVertex_coded]
  exact (hCol _ hPost v hv).trans (he.trans (hCol _ hPost w hw).symm)

/-- The whole-event neutrality test gives neutrality at every member
for any sublist of the fixed future list, using exact age restriction. -/
theorem resolvedDiaryAuxNeutral_member
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat)
    (k p : Nat) (hp0 : resolvedFairEventBoundary s0 k ≤ p)
    (hp1 : p < resolvedFairEventBoundary s0 (k+1))
    (h : resolvedDiaryAuxNeutral s0 S k)
    {d : Nat} (f : Fin d → Nat)
    (hf : ∀ i, f i ∈ resolvedDiaryFuture s0 S k) :
    (∀ i j : Fin d,
      (∀ q < p, resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 (f i)) =
        resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 (f j))) →
      resolvedFairEventEdge s0 p (resolvedFairEventCodePosition s0 (f i)) =
        resolvedFairEventEdge s0 p (resolvedFairEventCodePosition s0 (f j))) ∧
    resolvedTargetAge (resolvedFairEventEdge s0) 4 (Finset.range p)
      (fun i => resolvedFairEventCodePosition s0 (f i)) =
    resolvedTargetAge (resolvedFairEventEdge s0) 4 (Finset.range (p+1))
      (fun i => resolvedFairEventCodePosition s0 (f i)) := by
  classical
  constructor
  · intro i j hOld
    exact h.2 (f i) (hf i) (f j) (hf j)
      (fun q hq => hOld q (hq.trans_le hp0)) p hp0 hp1
  · let R := resolvedDiaryFuture s0 S k
    let r := R.orderEmbOfFin rfl
    have hRep (i : Fin d) : ∃ j : Fin R.card, r j = f i := by
      have hm : f i ∈ Set.range r := by
        change f i ∈ Set.range (R.orderEmbOfFin rfl)
        rw [R.range_orderEmbOfFin rfl]
        exact hf i
      exact hm
    let pi : Fin d → Fin R.card := fun i => Classical.choose (hRep i)
    have hEq : (fun i => resolvedFairEventCodePosition s0 (f i)) =
        (fun i => resolvedDiaryTarget s0 S k (pi i)) := by
      funext i
      exact congrArg (resolvedFairEventCodePosition s0) (Classical.choose_spec (hRep i)).symm
    have hBetween (b : Nat) (h0 : resolvedFairEventBoundary s0 k ≤ b)
        (h1 : b ≤ resolvedFairEventBoundary s0 (k+1)) :
        resolvedTargetAge (resolvedFairEventEdge s0) 4 (Finset.range b)
          (resolvedDiaryTarget s0 S k) =
        resolvedTargetAge (resolvedFairEventEdge s0) 4
          (Finset.range (resolvedFairEventBoundary s0 k)) (resolvedDiaryTarget s0 S k) :=
      resolvedTargetAge_neutral_between _ _ _ _ _
        (by intro q hq; exact Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le h0))
        (by intro q hq; exact Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le h1))
        h.1
    rw [hEq,resolvedTargetAge_reindex _ _ _ pi (by decide),
      resolvedTargetAge_reindex _ _ _ pi (by decide)]
    rw [hBetween p hp0 hp1.le,hBetween (p+1) (by omega) (by omega)]

/-- A selected original at or before the last selected index is retained
without adding another original. -/
theorem resolvedDiaryKeep_selected_address
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat)
    (n i : Nat) (hi : i ∈ S) (hBound : i ≤ n) :
    resolvedFairOriginalAddress s0 i ∈
      resolvedFairRetainedLevels s0 (resolvedDiaryKeep s0 S) n := by
  apply (oneGapPairedLevels_address_iff _ _).mpr
  apply (resolvedFairRetainedPositions_mem_iff s0 (resolvedDiaryKeep s0 S) n _).mpr
  refine ⟨(resolvedFairEventCodePosition_strictMono s0).monotone hBound,?_⟩
  rw [resolvedFairVertexEventIndex_codePosition]
  unfold resolvedDiaryKeep
  rw [resolvedFairSelectedKeep_code]
  exact decide_eq_true hi

/-- Both required local tests at every omitted meaningful coordinate
are derived from selected-only event retention. -/
theorem resolvedDiaryKeep_local_tests
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (n c : Nat)
    (hc : c ≤ resolvedFairRetainedTop s0 n)
    (ho : c ∉ resolvedFairRetainedLevels s0 (resolvedDiaryKeep s0 S) n)
    (hr : oneGapReal c) :
    let keep := resolvedDiaryKeep s0 S
    (∀ i j : Fin (resolvedNeutralCapFrontSize s0 keep n c),
      (∀ q < c, oneGapEdge (resolvedFairEventEdge s0) q (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) q (resolvedNeutralCapFront s0 keep n c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedNeutralCapFront s0 keep n c j)) ∧
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
      (resolvedNeutralCapFront s0 keep n c) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
      (resolvedNeutralCapFront s0 keep n c) := by
  classical
  dsimp only
  obtain ⟨p,rfl⟩ : ∃ p, c = oneGapAddress p :=
    ⟨oneGapIndex c,(oneGapAddress_index hr).symm⟩
  let k := resolvedFairVertexEventIndex s0 p
  let aux := resolvedDiaryAuxKeep s0 S
  let keep := resolvedDiaryKeep s0 S
  let c := oneGapAddress p
  have hkBounds := resolvedFairEventBoundary_bounds s0 p
  have hpBound : p ≤ resolvedFairEventCodePosition s0 n := by
    change oneGapAddress p ≤ oneGapAddress (resolvedFairEventCodePosition s0 n) at hc
    unfold oneGapAddress at hc
    omega
  have hk : keep k ≠ true := by
    intro he
    apply ho
    exact (oneGapPairedLevels_address_iff _ p).mpr
      ((resolvedFairRetainedPositions_mem_iff s0 keep n p).mpr ⟨hpBound,he⟩)
  by_cases hKind : (resolvedFairEvent s0 k).kind = .code
  · have hRole : resolvedFairEventRole s0 keep c = .coded (keep k) :=
      (resolvedFairEventRole_coded_iff s0 keep c (keep k)).mpr
        ⟨oneGapAddress_real p,by simpa only [c,oneGapIndex_address] using hKind,
          by simp only [c,oneGapIndex_address,k]⟩
    obtain ⟨m,hm,_⟩ := (resolvedFairEventRole_coded_iff_originalAddress
      s0 hEmpty keep c (keep k)).mp hRole
    change c = resolvedFairOriginalAddress s0 m at hm
    change (∀ i j : Fin (resolvedNeutralCapFrontSize s0 keep n c), _) ∧ _ 
    rw [hm]
    exact resolvedNeutralCapFront_code_neutral s0 hEmpty S aux n m
  · have hNeutral : resolvedDiaryAuxNeutral s0 S k := by
      by_contra hn
      apply hk
      change resolvedFairSelectedKeep s0 S aux k = true
      rw [resolvedFairSelectedKeep_auxiliary s0 S aux k hKind]
      change decide (¬ resolvedDiaryAuxNeutral s0 S k) = true
      exact decide_eq_true hn
    let N := resolvedNeutralCapSize s0 n
    let V := resolvedNeutralCapOldPool s0 keep n
    let f := resolvedFairSelectedFrontIndex s0 hEmpty S aux N V c
    have hAddr : ∀ i, resolvedNeutralCapFront s0 keep n c i =
        oneGapAddress (resolvedFairEventCodePosition s0 (f i)) :=
      resolvedFairSelectedFrontIndex_address s0 hEmpty S aux N V c
    have hf (i : Fin (resolvedNeutralCapFrontSize s0 keep n c)) :
        f i ∈ resolvedDiaryFuture s0 S k := by
      have hm := resolvedFairSelectedFrontIndex_mem s0 hEmpty S aux N V c i
      have hLater := resolvedFairSelectedFront_after_cut s0 keep N V c i
      change c < resolvedNeutralCapFront s0 keep n c i at hLater
      rw [hAddr i] at hLater
      change oneGapAddress p < oneGapAddress (resolvedFairEventCodePosition s0 (f i)) at hLater
      have hlt := oneGapAddress_strictMono.lt_iff_lt.mp hLater
      have hLe := resolvedFairVertexEventIndex_mono s0 hlt.le
      rw [resolvedFairVertexEventIndex_codePosition] at hLe
      have hNe : k ≠ resolvedFairCodingEvent s0 (f i) := by
        intro he
        apply hKind
        rw [he]
        exact (resolvedFairCodingEvent_spec s0 (f i)).1
      exact Finset.mem_filter.mpr ⟨hm,lt_of_le_of_ne hLe hNe⟩
    obtain ⟨hSplit,hAge⟩ := resolvedDiaryAuxNeutral_member s0 S k p
      hkBounds.1 hkBounds.2 hNeutral f hf
    have hFun : resolvedNeutralCapFront s0 keep n c =
        fun i => oneGapAddress (resolvedFairEventCodePosition s0 (f i)) := funext hAddr
    constructor
    · intro i j hOld
      rw [hAddr i,hAddr j] at hOld ⊢
      exact oneGap_noSplit_of_unpadded (resolvedFairEventEdge s0) _
        p (fun i => resolvedFairEventCodePosition s0 (f i)) hSplit i j hOld
    · rw [hFun]
      exact oneGap_canonicalAge_neutral_of_unpadded (resolvedFairEventEdge s0) 4 _
        p (fun i => resolvedFairEventCodePosition s0 (f i)) hAge

/-- No local graph-age or structural hypotheses remain for the selected
diary-retention envelope. -/
theorem resolvedDiarySelection_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (n : Nat) :
    let keep := resolvedDiaryKeep s0 S
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by decide))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by decide)))
        ({resolvedNeutralCapType s0 hEmpty n} : Set _) (resolvedNeutralCapTop s0 n) 0
        (resolvedNeutralCapPlan s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedNeutralCapPlan s0 keep n ∨
        resolvedNeutralCapTop s0 n < q} := by
  dsimp only
  exact resolvedNeutralCap_envelope s0 hEmpty (resolvedDiaryKeep s0 S) n
    (fun c hc ho hr => (resolvedDiaryKeep_local_tests s0 hEmpty S n c hc ho hr).1)
    (fun c hc ho hr => (resolvedDiaryKeep_local_tests s0 hEmpty S n c hc ho hr).2)

/-- Common genuine source codes for every selected original, with the
artificial cap removed from the source prefix. The ordinary retained
record is exactly that of the original graph with selected-only flags.
This is not yet the theorem identifying that record with a legal
abstract diary in the finite history machine. -/
theorem resolvedDiarySelection_sources
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) :
    let n := S.sup id
    let keep := resolvedDiaryKeep s0 S
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by decide))),
      ∀ i ∈ S, ∃ A : FiniteGPlusVertex (hensonForbiddenFamily 4 (by decide)),
        gPlusShapeImage F.map A = resolvedFairEventOneGapOriginal s0 hEmpty i ∧
        let R := (resolvedFairRetainedPositions s0 keep n).filter
          (fun p => p ≤ resolvedFairEventCodePosition s0 i)
        A.val = oneGapRetainedCode (resolvedFairEventEdge s0)
          (oneGapFinsetSelectionExtend R) R.card := by
  classical
  dsimp only
  let n := S.sup id
  let keep := resolvedDiaryKeep s0 S
  let I := resolvedNeutralCapPlan s0 keep n
  let top := resolvedNeutralCapTop s0 n
  obtain ⟨F,hInv,hRange⟩ := resolvedDiarySelection_envelope s0 hEmpty S n
  refine ⟨F,?_⟩
  intro i hi
  have hIn : i ≤ n := Finset.le_sup (f := id) hi
  have hRet := resolvedDiaryKeep_selected_address s0 S n i hi hIn
  obtain ⟨P,hVertex,hCap,hLower⟩ := resolvedNeutralCap_actualPair s0 hEmpty keep n i hIn hRet
  have hUpper : P.upper ∈ Set.range F.map := by
    rw [hCap]
    exact hInv.1.1 (subset_closure
      (admissibleKptSTree (hensonForbiddenFamily 4 (by decide)))
      (I : Set Nat) ({resolvedNeutralCapType s0 hEmpty n} : Set _) (by simp))
  have hBound : LevelTree.lev P.upper ≤ top := by
    rw [hCap,resolvedNeutralCapType_level]
    exact Nat.sub_le _ _
  obtain ⟨Q,hQ⟩ := retained_pair_bounded_lift F I top hRange P hUpper hBound hLower
  have hImage := hQ.trans hVertex
  refine ⟨Q.val.vertex,hImage,?_⟩
  let R := resolvedFairRetainedPositions s0 keep n
  let p := resolvedFairEventCodePosition s0 i
  let b := resolvedFairEventCodePosition s0 n
  have hp : p ≤ b := (resolvedFairEventCodePosition_strictMono s0).monotone hIn
  have hpTop : oneGapAddress p ≤ top :=
    oneGapAddress_strictMono.monotone (hp.trans (Nat.le_succ b))
  have hFilter : (insert (b+1) R).filter (fun j => j ≤ p) =
      R.filter (fun j => j ≤ p) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨h,hj⟩
      rcases h with rfl | h
      · omega
      · exact ⟨h,hj⟩
    · rintro ⟨h,hj⟩
      exact ⟨Or.inr h,hj⟩
  have hCode := oneGap_inverseSource_code F (resolvedFairEventEdge s0)
    (insert (b+1) R) top p hRange hpTop Q.val.vertex
    (congrArg (fun v => v.val) hImage)
  rw [hFilter] at hCode
  exact hCode

end Kk
