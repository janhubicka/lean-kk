import Kk.ResolvedFairEventSchedule
import Kk.OneGapAgeTransport

/-!
# Coding neutrality in the actual chronological graph

English proof reviewed before implementation:
`docs/resolved_fair_coding_neutrality_english_20261127.md`.
Use the chosen event's actual code certificate and exact prefix images.
Terminal lists consist of later originals and may repeat or be empty.
-/

namespace Kk

/-- The actual code certificate preserves the complete age on any
surviving fixed terminal list. No equality of raw ages is asserted. -/
theorem ResolvedEventCertificate.code_targetAge_neutral
    {W : Set Nat} {r : Nat} {e : ResolvedEvent} {d : Nat}
    (h : ResolvedEventCertificate W r e) (hCode : e.kind = .code)
    (target : Fin d → Nat) (hTarget : ∀ i, target i ∈ W ∧ target i ≠ r) :
    resolvedTargetAge e.edge 4 e.preOld target =
      resolvedTargetAge e.edge 4 e.postOld target := by
  cases h with
  | marker => simp at hCode
  | cover => simp at hCode
  | code s hr hSat hExact hSingleton hConst =>
      change resolvedTargetAge s.edge 4 s.old target =
        resolvedTargetAge s.edge 4 (s.old ∪ [r].toFinset) target
      have hPost : s.old ∪ [r].toFinset = insert r s.old := by
        ext x
        simp
      rw [hPost]
      exact (s.saturatedCode_target_neutral r hr (by decide)
        hSingleton hConst hSat target hTarget).symm

/-- At an actual code event, equality of complete old columns implies
equality of the new coding bit. -/
theorem ResolvedEventCertificate.code_no_split
    {W : Set Nat} {r : Nat} {e : ResolvedEvent}
    (h : ResolvedEventCertificate W r e) (hCode : e.kind = .code)
    (v w : Nat) (hv : v ∈ W) (hw : w ∈ W)
    (hOld : ∀ p ∈ e.preOld, e.edge p v = e.edge p w) :
    e.edge r v = e.edge r w := by
  cases h with
  | marker => simp at hCode
  | cover => simp at hCode
  | code s hr hSat hExact hSingleton hConst =>
      exact hConst v hv w hw ((hExact v hv w hw).2 hOld)

theorem resolvedFairCodingEvent_location
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairEventLocation s0 (resolvedFairCodingEvent s0 n) =
      ⟨n, resolvedFairRoundCodeIndex s0 n⟩ := by
  unfold resolvedFairEventLocation resolvedFairCodingEvent resolvedFairEventPosition
  exact oneGapBatchLocation_position _ (resolvedFairRoundEvents_positive s0) _

/-- The certificate belongs to the actual chosen event in its known round. -/
theorem resolvedFairCodingEvent_certificate
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    ResolvedEventCertificate (resolvedEvenTail n) (2*n)
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)) := by
  simpa only [resolvedFairCodingEvent_location] using
    resolvedFairEvent_certificate s0 (resolvedFairCodingEvent s0 n)

/-- The chronological prefix is exactly the chosen code event's old pool. -/
theorem resolvedFairEventCoding_prefix_image
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) :
    (Finset.range (resolvedFairEventCodePosition s0 n)).image
        (resolvedFairEventVertex s0) =
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).preOld := by
  classical
  ext v
  simpa only [Finset.mem_image, Finset.mem_range, resolvedFairEventCodePosition] using
    resolvedFairEventVertex_prefix s0 hEmpty (resolvedFairCodingEvent s0 n) v

/-- Including the singleton coding position gives precisely its post-old pool. -/
theorem resolvedFairEventCoding_prefix_succ_image
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) :
    (Finset.range (resolvedFairEventCodePosition s0 n + 1)).image
        (resolvedFairEventVertex s0) =
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).postOld := by
  classical
  rw [Finset.range_add_one, Finset.image_insert, resolvedFairEventVertex_coded,
    resolvedFairEventCoding_prefix_image s0 hEmpty n]
  have hBlock := (resolvedFairCodingEvent_spec s0 n).2
  ext v
  simp [ResolvedEvent.postOld, hBlock, or_comm]

private theorem coding_original_live (n m : Nat) (h : n ≤ m) :
    2*m ∈ resolvedEvenTail n := by
  change (2*m) % 2 = 0 ∧ 2*n ≤ 2*m
  omega

private theorem coding_event_agreement
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n x y : Nat)
    (hx : x ∈ (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).postOld ∨
      x ∈ resolvedEvenTail n)
    (hy : y ∈ (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).postOld ∨
      y ∈ resolvedEvenTail n) :
    resolvedFairEdge s0 x y =
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge x y := by
  apply resolvedFairEvent_agreement s0 (resolvedFairCodingEvent s0 n) x y
  · simpa only [resolvedFairCodingEvent_location] using hx
  · simpa only [resolvedFairCodingEvent_location] using hy

private theorem coding_prefix_mem_postOld
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n q : Nat) (hq : q ≤ resolvedFairEventCodePosition s0 n) :
    resolvedFairEventVertex s0 q ∈
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).postOld := by
  rw [← resolvedFairEventCoding_prefix_succ_image s0 hEmpty n]
  exact Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le hq), rfl⟩

private theorem coding_column_eq
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n q m : Nat) (hq : q ≤ resolvedFairEventCodePosition s0 n) (hm : n ≤ m) :
    resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 m) =
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge
        (resolvedFairEventVertex s0 q) (2*m) := by
  unfold resolvedFairEventEdge
  rw [resolvedFairEventVertex_coded]
  exact coding_event_agreement s0 n _ _
    (Or.inl (coding_prefix_mem_postOld s0 hEmpty n q hq))
    (Or.inr (coding_original_live n m hm))

private theorem coding_targetAge_transport
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) {d : Nat} (target : Fin d → Nat) (hTarget : ∀ i, n < target i)
    (P : Finset Nat)
    (hP : P ⊆ Finset.range (resolvedFairEventCodePosition s0 n + 1)) :
    resolvedTargetAge (resolvedFairEventEdge s0) 4 P
        (fun i => resolvedFairEventCodePosition s0 (target i)) =
      resolvedTargetAge (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge 4
        (P.image (resolvedFairEventVertex s0)) (fun i => 2*target i) := by
  have hLe : ∀ q ∈ P, q ≤ resolvedFairEventCodePosition s0 n := by
    intro q hq
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (hP hq))
  unfold resolvedTargetAge
  symm
  apply integerGraphAgeCanonical_induced_image_eq
    (resolvedFairEventEdge s0)
    (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge 4 d P
    (fun q i => resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 (target i)))
    (fun q i => (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge q (2*target i))
    (resolvedFairEventVertex s0) (resolvedFairEventVertex_injective s0 hEmpty)
  · intro x hx y hy _hxy
    exact (coding_event_agreement s0 n _ _
      (Or.inl (coding_prefix_mem_postOld s0 hEmpty n x (hLe x hx)))
      (Or.inl (coding_prefix_mem_postOld s0 hEmpty n y (hLe y hy)))).symm
  · intro q hq i
    exact (coding_column_eq s0 hEmpty n q (target i) (hLe q hq)
      (Nat.le_of_lt (hTarget i))).symm

/-- The complete chronological canonical age is unchanged by actual coding,
for any finite list of strictly later originals, including repeats or none. -/
theorem resolvedFairEventCoding_targetAge_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) {d : Nat} (target : Fin d → Nat) (hTarget : ∀ i, n < target i) :
    resolvedTargetAge (resolvedFairEventEdge s0) 4
        (Finset.range (resolvedFairEventCodePosition s0 n))
        (fun i => resolvedFairEventCodePosition s0 (target i)) =
      resolvedTargetAge (resolvedFairEventEdge s0) 4
        (Finset.range (resolvedFairEventCodePosition s0 n + 1))
        (fun i => resolvedFairEventCodePosition s0 (target i)) := by
  have hBefore := coding_targetAge_transport s0 hEmpty n target hTarget
    (Finset.range (resolvedFairEventCodePosition s0 n)) (by
      intro q hq
      apply Finset.mem_range.mpr
      have h := Finset.mem_range.mp hq
      omega)
  rw [resolvedFairEventCoding_prefix_image s0 hEmpty n] at hBefore
  have hAfter := coding_targetAge_transport s0 hEmpty n target hTarget
    (Finset.range (resolvedFairEventCodePosition s0 n + 1)) (Finset.Subset.refl _)
  rw [resolvedFairEventCoding_prefix_succ_image s0 hEmpty n] at hAfter
  have hNeutral := (resolvedFairCodingEvent_certificate s0 n).code_targetAge_neutral
    (resolvedFairCodingEvent_spec s0 n).1 (fun i => 2*target i) (by
      intro i
      refine ⟨coding_original_live n (target i) (Nat.le_of_lt (hTarget i)), ?_⟩
      have h := hTarget i
      omega)
  exact hBefore.trans (hNeutral.trans hAfter.symm)

/-- Equality of the complete chronological old columns is not split by
the next actual coding bit on two surviving original terminals. -/
theorem resolvedFairEventCoding_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n v w : Nat) (hv : n < v) (hw : n < w)
    (hOld : ∀ q, q < resolvedFairEventCodePosition s0 n →
      resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 v) =
        resolvedFairEventEdge s0 q (resolvedFairEventCodePosition s0 w)) :
    resolvedFairEventEdge s0 (resolvedFairEventCodePosition s0 n)
        (resolvedFairEventCodePosition s0 v) =
      resolvedFairEventEdge s0 (resolvedFairEventCodePosition s0 n)
        (resolvedFairEventCodePosition s0 w) := by
  have hOldActual : ∀ x ∈ (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).preOld,
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge x (2*v) =
        (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).edge x (2*w) := by
    intro x hx
    rw [← resolvedFairEventCoding_prefix_image s0 hEmpty n] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hq' := Finset.mem_range.mp hq
    exact (coding_column_eq s0 hEmpty n q v (Nat.le_of_lt hq') (Nat.le_of_lt hv)).symm.trans
      ((hOld q hq').trans
        (coding_column_eq s0 hEmpty n q w (Nat.le_of_lt hq') (Nat.le_of_lt hw)))
  have hActual := (resolvedFairCodingEvent_certificate s0 n).code_no_split
    (resolvedFairCodingEvent_spec s0 n).1 (2*v) (2*w)
    (coding_original_live n v (Nat.le_of_lt hv))
    (coding_original_live n w (Nat.le_of_lt hw)) hOldActual
  have hV := coding_column_eq s0 hEmpty n (resolvedFairEventCodePosition s0 n) v
    le_rfl (Nat.le_of_lt hv)
  have hW := coding_column_eq s0 hEmpty n (resolvedFairEventCodePosition s0 n) w
    le_rfl (Nat.le_of_lt hw)
  rw [resolvedFairEventVertex_coded] at hV hW
  exact hV.trans (hActual.trans hW.symm)

end Kk
