import Kk.ResolvedRoundEvents
import Kk.ResolvedEventChainOrder
import Kk.ResolvedFairChronological
import Kk.OneGapEventScheduleOrder

/-!
# The actual fair graph in individual-event order

English proof and review: `docs/resolved_event_schedule_english_20261127.md`.
The first enumeration orders actual event occurrences; the second orders
their positive vertex blocks. Cover-path order is retained throughout.
-/

namespace Kk

theorem resolvedFairRound_exists_event_list
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    ∃ events : List ResolvedEvent,
      ResolvedEventChain (resolvedEvenTail n) (2*n)
        (resolvedFairStages s0 (n+1)).edge (resolvedFairStages s0 n).old
        events (resolvedFairStages s0 (n+1)).old ∧
      ∃ aux code, events = aux ++ [code] ∧
        (∀ e ∈ aux, e.kind ≠ .code) ∧ code.kind = .code ∧ code.block = [2*n] := by
  obtain ⟨aux,code,hChain,hAux,hKind,hBlock⟩ :=
    (resolvedFairStages_step s0 n).exists_events (resolvedEvenTail_coding n)
  exact ⟨aux ++ [code],hChain,aux,code,rfl,hAux,hKind,hBlock⟩

noncomputable def resolvedFairRoundEvents
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : List ResolvedEvent :=
  Classical.choose (resolvedFairRound_exists_event_list s0 n)

theorem resolvedFairRoundEvents_chain
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    ResolvedEventChain (resolvedEvenTail n) (2*n)
      (resolvedFairStages s0 (n+1)).edge (resolvedFairStages s0 n).old
      (resolvedFairRoundEvents s0 n) (resolvedFairStages s0 (n+1)).old :=
  (Classical.choose_spec (resolvedFairRound_exists_event_list s0 n)).1

theorem resolvedFairRoundEvents_last
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    ∃ aux code, resolvedFairRoundEvents s0 n = aux ++ [code] ∧
      (∀ e ∈ aux, e.kind ≠ .code) ∧ code.kind = .code ∧ code.block = [2*n] :=
  (Classical.choose_spec (resolvedFairRound_exists_event_list s0 n)).2

theorem resolvedFairRoundEvents_positive
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    0 < (resolvedFairRoundEvents s0 n).length := by
  obtain ⟨aux,code,hList,_⟩ := resolvedFairRoundEvents_last s0 n
  rw [hList]
  simp

noncomputable def resolvedFairEventPosition
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat)
    (i : Fin (resolvedFairRoundEvents s0 n).length) : Nat :=
  oneGapBatchPosition (fun m => (resolvedFairRoundEvents s0 m).length) ⟨n,i⟩

noncomputable def resolvedFairEventLocation
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) :
    (n : Nat) × Fin (resolvedFairRoundEvents s0 n).length :=
  oneGapBatchLocation (fun n => (resolvedFairRoundEvents s0 n).length)
    (resolvedFairRoundEvents_positive s0) k

noncomputable def resolvedFairEvent
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Nat → ResolvedEvent :=
  oneGapChronologicalVertex (resolvedFairRoundEvents s0) (resolvedFairRoundEvents_positive s0)

theorem resolvedFairEvent_at_position
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat)
    (i : Fin (resolvedFairRoundEvents s0 n).length) :
    resolvedFairEvent s0 (resolvedFairEventPosition s0 n i) =
      (resolvedFairRoundEvents s0 n)[i.val] :=
  oneGapChronologicalVertex_at_position _ (resolvedFairRoundEvents_positive s0) n i

theorem resolvedFairEvent_certificate
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) :
    ResolvedEventCertificate (resolvedEvenTail (resolvedFairEventLocation s0 k).1)
      (2*(resolvedFairEventLocation s0 k).1) (resolvedFairEvent s0 k) :=
  (resolvedFairRoundEvents_chain s0 _).event_certificate
    (oneGapChronologicalVertex_mem _ (resolvedFairRoundEvents_positive s0) k)

/-- Every recorded event table agrees with the single actual limit on
its post-old pool and the original live set of its round. -/
theorem resolvedFairEvent_agreement
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k x y : Nat)
    (hx : x ∈ (resolvedFairEvent s0 k).postOld ∨
      x ∈ resolvedEvenTail (resolvedFairEventLocation s0 k).1)
    (hy : y ∈ (resolvedFairEvent s0 k).postOld ∨
      y ∈ resolvedEvenTail (resolvedFairEventLocation s0 k).1) :
    resolvedFairEdge s0 x y = (resolvedFairEvent s0 k).edge x y := by
  let n := (resolvedFairEventLocation s0 k).1
  have hMem : resolvedFairEvent s0 k ∈ resolvedFairRoundEvents s0 n :=
    oneGapChronologicalVertex_mem _ (resolvedFairRoundEvents_positive s0) k
  have hChain := resolvedFairRoundEvents_chain s0 n
  have hSub := hChain.event_postOld_subset hMem
  have hDomain : ∀ v, v ∈ (resolvedFairEvent s0 k).postOld ∨ v ∈ resolvedEvenTail n →
      v ∈ (resolvedFairStages s0 (n+1)).old ∨ v ∈ resolvedEvenTail (n+1) := by
    intro v hv
    rcases hv with hp | hw
    · exact Or.inl (hSub hp)
    · exact resolvedFairStages_live_mono_step s0 n v (Or.inr hw)
  exact (resolvedFairEdge_eq_live_at s0 (n+1) x y (hDomain x hx) (hDomain y hy)).trans
    (hChain.event_agreement hMem x y hx hy)

/-- Earlier global event occurrences are exactly earlier rounds and
the earlier events inside this round, with their actual vertex blocks. -/
theorem resolvedFairEvent_prior_blocks
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (i : Fin (resolvedFairRoundEvents s0 n).length) (v : Nat) :
    (∃ k, k < resolvedFairEventPosition s0 n i ∧ v ∈ (resolvedFairEvent s0 k).block) ↔
      v ∈ (resolvedFairStages s0 n).old ∨
      ∃ j : Fin (resolvedFairRoundEvents s0 n).length,
        j.val < i.val ∧ v ∈ ((resolvedFairRoundEvents s0 n)[j.val]).block := by
  constructor
  · rintro ⟨k,hk,hv⟩
    have hOrder := (oneGapChronologicalVertex_prefix_at_entry
      (resolvedFairRoundEvents s0) (resolvedFairRoundEvents_positive s0)
      n i (resolvedFairEvent s0 k)).mp ⟨k,hk,rfl⟩
    rcases hOrder with ⟨m,hm,he⟩ | ⟨j,hj,he⟩
    · have hFlatten : v ∈ resolvedEventVertices (resolvedFairRoundEvents s0 m) :=
        List.mem_flatMap.mpr ⟨resolvedFairEvent s0 k,he,hv⟩
      have hOld := ((resolvedFairRoundEvents_chain s0 m).vertices_mem v).mp hFlatten
      exact Or.inl (resolvedFairStages_old_mono s0 (show m+1 ≤ n from hm) hOld.1)
    · exact Or.inr ⟨j,hj,he.symm ▸ hv⟩
  · rintro (hv | ⟨j,hj,hv⟩)
    · obtain ⟨m,hm,hNew⟩ := (resolvedFairRoundNew_prefix s0 hEmpty n v).mpr hv
      have hFlatten := ((resolvedFairRoundEvents_chain s0 m).vertices_mem v).mpr
        (Finset.mem_sdiff.mp hNew)
      obtain ⟨e,he,hv⟩ := List.mem_flatMap.mp hFlatten
      obtain ⟨k,hk,hEq⟩ := (oneGapChronologicalVertex_prefix_at_entry
        (resolvedFairRoundEvents s0) (resolvedFairRoundEvents_positive s0) n i e).mpr
          (Or.inl ⟨m,hm,he⟩)
      have hEq' : resolvedFairEvent s0 k = e := hEq
      exact ⟨k,hk,hEq'.symm ▸ hv⟩
    · obtain ⟨k,hk,hEq⟩ := (oneGapChronologicalVertex_prefix_at_entry
        (resolvedFairRoundEvents s0) (resolvedFairRoundEvents_positive s0)
        n i ((resolvedFairRoundEvents s0 n)[j.val])).mpr (Or.inr ⟨j,hj,rfl⟩)
      have hEq' : resolvedFairEvent s0 k = (resolvedFairRoundEvents s0 n)[j.val] := hEq
      exact ⟨k,hk,hEq'.symm ▸ hv⟩

theorem resolvedFairEvent_preOld_at_position
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n : Nat) (i : Fin (resolvedFairRoundEvents s0 n).length) (v : Nat) :
    v ∈ (resolvedFairEvent s0 (resolvedFairEventPosition s0 n i)).preOld ↔
      ∃ k, k < resolvedFairEventPosition s0 n i ∧ v ∈ (resolvedFairEvent s0 k).block := by
  rw [resolvedFairEvent_at_position]
  exact ((resolvedFairRoundEvents_chain s0 n).preOld_iff i v).trans
    (resolvedFairEvent_prior_blocks s0 hEmpty n i v).symm

theorem resolvedFairEvent_preOld_iff
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k v : Nat) :
    v ∈ (resolvedFairEvent s0 k).preOld ↔
      ∃ j, j < k ∧ v ∈ (resolvedFairEvent s0 j).block := by
  let tag := resolvedFairEventLocation s0 k
  have hPos : resolvedFairEventPosition s0 tag.1 tag.2 = k :=
    oneGapBatchPosition_location _ (resolvedFairRoundEvents_positive s0) k
  simpa only [hPos] using
    resolvedFairEvent_preOld_at_position s0 hEmpty tag.1 tag.2 v

noncomputable def resolvedFairEventBlock
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) : List Nat :=
  (resolvedFairEvent s0 k).block

theorem resolvedFairEventBlock_positive
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) :
    0 < (resolvedFairEventBlock s0 k).length :=
  (resolvedFairEvent_certificate s0 k).block_pos

theorem resolvedFairEventBlock_nodup
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) :
    (resolvedFairEventBlock s0 k).Nodup :=
  (resolvedFairEvent_certificate s0 k).block_nodup

theorem resolvedFairEventBlock_disjoint
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (i j : Nat) (hij : i ≠ j) :
    List.Disjoint (resolvedFairEventBlock s0 i) (resolvedFairEventBlock s0 j) := by
  have hOrdered : ∀ a b : Nat, a < b →
      List.Disjoint (resolvedFairEventBlock s0 a) (resolvedFairEventBlock s0 b) := by
    intro a b hab v ha hb
    have hp := (resolvedFairEvent_preOld_iff s0 hEmpty b v).mpr ⟨a,hab,ha⟩
    exact (Finset.disjoint_left.mp (resolvedFairEvent_certificate s0 b).block_fresh)
      hp (List.mem_toFinset.mpr hb)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hOrdered i j hlt
  · exact (hOrdered j i hgt).symm

noncomputable def resolvedFairEventBoundary
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Nat → Nat :=
  oneGapBatchBoundary (fun k => (resolvedFairEventBlock s0 k).length)

noncomputable def resolvedFairEventVertex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) : Nat → Nat :=
  oneGapChronologicalVertex (resolvedFairEventBlock s0) (resolvedFairEventBlock_positive s0)

theorem resolvedFairEventVertex_injective
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    Function.Injective (resolvedFairEventVertex s0) :=
  oneGapChronologicalVertex_injective _ (resolvedFairEventBlock_positive s0)
    (resolvedFairEventBlock_nodup s0) (resolvedFairEventBlock_disjoint s0 hEmpty)

/-- Every event boundary is exactly its actual recorded old pool. -/
theorem resolvedFairEventVertex_prefix
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k v : Nat) :
    (∃ p, p < resolvedFairEventBoundary s0 k ∧ resolvedFairEventVertex s0 p = v) ↔
      v ∈ (resolvedFairEvent s0 k).preOld := by
  change (∃ p, p < oneGapBatchBoundary _ k ∧
    oneGapChronologicalVertex _ _ p = v) ↔ _
  rw [oneGapChronologicalVertex_prefix]
  exact (resolvedFairEvent_preOld_iff s0 hEmpty k v).symm

/-- Inside a block, the chronological prefix adds precisely its earlier
entries to the actual event pre-pool. -/
theorem resolvedFairEventVertex_prefix_inside
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (k : Nat) (i : Fin (resolvedFairEventBlock s0 k).length) (v : Nat) :
    (∃ p, p < oneGapBatchPosition (fun j => (resolvedFairEventBlock s0 j).length)
        ⟨k,i⟩ ∧ resolvedFairEventVertex s0 p = v) ↔
      v ∈ (resolvedFairEvent s0 k).preOld ∨
      ∃ j : Fin (resolvedFairEventBlock s0 k).length,
        j.val < i.val ∧ (resolvedFairEventBlock s0 k)[j.val] = v := by
  change (∃ p, p < oneGapBatchPosition
    (fun j => (resolvedFairEventBlock s0 j).length) ⟨k,i⟩ ∧
    oneGapChronologicalVertex (resolvedFairEventBlock s0)
      (resolvedFairEventBlock_positive s0) p = v) ↔ _
  rw [oneGapChronologicalVertex_prefix_at_entry]
  exact or_congr (resolvedFairEvent_preOld_iff s0 hEmpty k v).symm Iff.rfl

theorem resolvedFairEventVertex_range
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (v : Nat) :
    (∃ p, resolvedFairEventVertex s0 p = v) ↔ v ∈ resolvedFairDomain s0 := by
  constructor
  · rintro ⟨p,hp⟩
    have hBlock := oneGapChronologicalVertex_mem (resolvedFairEventBlock s0)
      (resolvedFairEventBlock_positive s0) p
    let k := (oneGapBatchLocation (fun j => (resolvedFairEventBlock s0 j).length)
      (resolvedFairEventBlock_positive s0) p).1
    have hv : v ∈ (resolvedFairEvent s0 k).block := hp ▸ hBlock
    let n := (resolvedFairEventLocation s0 k).1
    have hMem : resolvedFairEvent s0 k ∈ resolvedFairRoundEvents s0 n :=
      oneGapChronologicalVertex_mem _ (resolvedFairRoundEvents_positive s0) k
    have hOld := (resolvedFairRoundEvents_chain s0 n).event_postOld_subset hMem
      (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hv)))
    exact ⟨n+1,hOld⟩
  · rintro ⟨n,hv⟩
    let i : Fin (resolvedFairRoundEvents s0 n).length :=
      ⟨0,resolvedFairRoundEvents_positive s0 n⟩
    have hPre : v ∈ ((resolvedFairRoundEvents s0 n)[i.val]).preOld :=
      ((resolvedFairRoundEvents_chain s0 n).preOld_iff i v).mpr (Or.inl hv)
    have hPre' : v ∈ (resolvedFairEvent s0 (resolvedFairEventPosition s0 n i)).preOld := by
      rw [resolvedFairEvent_at_position]
      exact hPre
    obtain ⟨p,_hp,hpv⟩ :=
      (resolvedFairEventVertex_prefix s0 hEmpty (resolvedFairEventPosition s0 n i) v).mpr hPre'
    exact ⟨p,hpv⟩

noncomputable def resolvedFairRoundCodeIndex
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    Fin (resolvedFairRoundEvents s0 n).length :=
  ⟨(resolvedFairRoundEvents s0 n).length - 1,by
    have h := resolvedFairRoundEvents_positive s0 n
    omega⟩

noncomputable def resolvedFairCodingEvent
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  resolvedFairEventPosition s0 n (resolvedFairRoundCodeIndex s0 n)

theorem resolvedFairCodingEvent_spec
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).kind = .code ∧
      (resolvedFairEvent s0 (resolvedFairCodingEvent s0 n)).block = [2*n] := by
  unfold resolvedFairCodingEvent
  rw [resolvedFairEvent_at_position]
  obtain ⟨aux,code,hList,_hAux,hKind,hBlock⟩ := resolvedFairRoundEvents_last s0 n
  simpa [resolvedFairRoundCodeIndex,hList] using And.intro hKind hBlock

theorem resolvedFairCodingEvent_strictMono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    StrictMono (resolvedFairCodingEvent s0) := by
  intro n m hnm
  exact (oneGapBatchPosition_lt_iff _ (resolvedFairRoundEvents_positive s0) _ _).mpr
    (Or.inl hnm)

noncomputable def resolvedFairEventCodePosition
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) : Nat :=
  resolvedFairEventBoundary s0 (resolvedFairCodingEvent s0 n)

theorem resolvedFairEventVertex_coded
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (n : Nat) :
    resolvedFairEventVertex s0 (resolvedFairEventCodePosition s0 n) = 2*n := by
  let k := resolvedFairCodingEvent s0 n
  have hBlock : resolvedFairEventBlock s0 k = [2*n] := (resolvedFairCodingEvent_spec s0 n).2
  have h := oneGapChronologicalVertex_at_position (resolvedFairEventBlock s0)
    (resolvedFairEventBlock_positive s0) k ⟨0,resolvedFairEventBlock_positive s0 k⟩
  simpa [oneGapBatchPosition,resolvedFairEventCodePosition,resolvedFairEventBoundary,
    resolvedFairEventVertex,k,hBlock] using h

theorem resolvedFairEventCodePosition_strictMono
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) :
    StrictMono (resolvedFairEventCodePosition s0) :=
  (oneGapBatchBoundary_strictMono _ (resolvedFairEventBlock_positive s0)).comp
    (resolvedFairCodingEvent_strictMono s0)

noncomputable def resolvedFairEventEdge
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u v : Nat) : Bool :=
  resolvedFairEdge s0 (resolvedFairEventVertex s0 u) (resolvedFairEventVertex s0 v)

theorem resolvedFairEventEdge_sym
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u v : Nat) :
    resolvedFairEventEdge s0 u v = resolvedFairEventEdge s0 v u :=
  resolvedFairEdge_sym s0 _ _

theorem resolvedFairEventEdge_loops
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (u : Nat) :
    resolvedFairEventEdge s0 u u = false :=
  resolvedFairEdge_loops s0 _

theorem resolvedFairEventEdge_free
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    ∀ C : Finset Nat, IsDirectedCliqueOn (resolvedFairEventEdge s0) C → C.card < 4 := by
  classical
  intro C hC
  have hClique : IsDirectedCliqueOn (resolvedFairEdge s0)
      (C.image (resolvedFairEventVertex s0)) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact hC a ha b hb (fun he => hxy (congrArg (resolvedFairEventVertex s0) he))
  have hFree := resolvedFairEdge_free s0 _ hClique
  have hCard := Finset.card_image_of_injective C (resolvedFairEventVertex_injective s0 hEmpty)
  rwa [hCard] at hFree

theorem resolvedFairEventEdge_originals
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (i j : Nat) :
    resolvedFairEventEdge s0 (resolvedFairEventCodePosition s0 i)
      (resolvedFairEventCodePosition s0 j) = s0.edge (2*i) (2*j) := by
  unfold resolvedFairEventEdge
  rw [resolvedFairEventVertex_coded,resolvedFairEventVertex_coded]
  exact resolvedFairEdge_even_eq s0 i j

theorem resolvedInitialEventGraph_originals
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (i j : Nat) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    resolvedFairEventEdge s0 (resolvedFairEventCodePosition s0 i)
      (resolvedFairEventCodePosition s0 j) = E i j := by
  dsimp only
  rw [resolvedFairEventEdge_originals]
  change E (2*i/2) (2*j/2) = E i j
  congr 1 <;> omega

end Kk
