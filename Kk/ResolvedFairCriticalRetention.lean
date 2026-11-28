import Kk.ResolvedFairAuxiliaryEnvelope
import Kk.FixedTerminalCriticalCuts

/-!
# Controlled auxiliary retention for actual K4 one-gap envelopes

Keep whole auxiliary occurrences touched by a fixed-terminal critical
cut. Coding flags are unchanged. The fixed terminal set contains all
selected original addresses and the fresh cap. The resulting bound is
coarse and does not identify the sharp diary or its labelled orbit.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

noncomputable def resolvedFairFixedTerminals
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) : Finset Nat :=
  (resolvedFairSelectionWithCap S).image (resolvedFairOriginalAddress s0)

theorem resolvedFairFixedTerminals_card
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) :
    (resolvedFairFixedTerminals s0 S).card = S.card + 1 := by
  rw [resolvedFairFixedTerminals, Finset.card_image_of_injective _
    (resolvedFairOriginalAddress_strictMono s0).injective, resolvedFairSelectionWithCap_card]

noncomputable def resolvedFairCriticalEvents
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) : Finset Nat :=
  (fixedCriticalCuts (oneGapEdge (resolvedFairEventEdge s0))
    (resolvedFairFixedTerminals s0 S)
    (resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))).image
      (fun c => resolvedFairVertexEventIndex s0 (oneGapIndex c))

noncomputable def resolvedFairCriticalAuxKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat)
    (k : Nat) : Bool :=
  decide (k ∈ resolvedFairCriticalEvents s0 S)

noncomputable def resolvedFairCriticalKeep
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) : Nat → Bool :=
  resolvedFairFiniteKeep s0 S (resolvedFairCriticalAuxKeep s0 S)

/-- The actual moving front is a sublist of the fixed set, irrespective
of auxiliary flags. No equality of dependent front types is needed. -/
theorem resolvedFairRetainedFront_mem_fixed
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (c : Nat)
    (i : Fin (resolvedFairRetainedFrontSize s0 (resolvedFairFiniteKeep s0 S auxKeep)
      (resolvedFairSelectionCap S) c)) :
    resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S auxKeep)
      (resolvedFairSelectionCap S) c i ∈ resolvedFairFixedTerminals s0 S := by
  classical
  obtain ⟨n, hn, hAddr⟩ := resolvedFairSelectedFront_original s0 hEmpty
    (resolvedFairSelectionWithCap S) auxKeep
    (resolvedFairRetainedSize s0 (resolvedFairSelectionCap S))
    (resolvedFairRetainedPool s0 (resolvedFairFiniteKeep s0 S auxKeep)
      (resolvedFairSelectionCap S)) c i
  exact Finset.mem_image.mpr ⟨n, hn, hAddr.symm⟩

/-- An omitted meaningful cut either is a genuine coding coordinate or
has unchanged fixed-terminal rank. Whole-block flags are essential. -/
theorem resolvedFairCriticalCut_code_or_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hc : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (ho : c ∉ resolvedFairRetainedLevels s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S)) (hr : oneGapReal c) :
    (∃ n, c = resolvedFairOriginalAddress s0 n) ∨
      fixedCriticalRank (oneGapEdge (resolvedFairEventEdge s0))
        (resolvedFairFixedTerminals s0 S) c =
      fixedCriticalRank (oneGapEdge (resolvedFairEventEdge s0))
        (resolvedFairFixedTerminals s0 S) (c+1) := by
  classical
  let k := resolvedFairVertexEventIndex s0 (oneGapIndex c)
  let keep := resolvedFairCriticalKeep s0 S
  by_cases hKind : (resolvedFairEvent s0 k).kind = .code
  · have hRole : resolvedFairEventRole s0 keep c = .coded (keep k) :=
      (resolvedFairEventRole_coded_iff s0 keep c (keep k)).mpr ⟨hr,hKind,rfl⟩
    obtain ⟨n,hn,_⟩ :=
      (resolvedFairEventRole_coded_iff_originalAddress s0 hEmpty keep c (keep k)).mp hRole
    exact Or.inl ⟨n,hn⟩
  · right
    apply fixedCriticalRank_eq_of_not_mem _ _
      (resolvedFairRetainedTop s0 (resolvedFairSelectionCap S)) c hc
    intro hCritical
    have hEvent : k ∈ resolvedFairCriticalEvents s0 S :=
      Finset.mem_image.mpr ⟨c,hCritical,rfl⟩
    have hKeep : keep k = true := by
      change resolvedFairSelectedKeep s0 (resolvedFairSelectionWithCap S)
        (resolvedFairCriticalAuxKeep s0 S) k = true
      rw [resolvedFairSelectedKeep_auxiliary _ _ _ _ hKind]
      simp [resolvedFairCriticalAuxKeep, hEvent]
    have hRole : resolvedFairEventRole s0 keep c = .auxiliary k true :=
      (resolvedFairEventRole_auxiliary_iff s0 keep c k true).mpr
        ⟨hr,rfl,hKind,hKeep⟩
    exact ho (resolvedFairRetainedLevels_of_retained_real s0 keep
      (resolvedFairSelectionCap S) c (Nat.le_of_lt hc) hr
      (Or.inr (Or.inr ⟨k,hRole⟩)))

/-- At a coding coordinate, the actual front consists of surviving
originals for every auxiliary keep function. -/
theorem resolvedFairFiniteFront_code_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat) :
    let keep := resolvedFairFiniteKeep s0 S auxKeep
    let cap := resolvedFairSelectionCap S
    let c := resolvedFairOriginalAddress s0 n
    ∀ i j : Fin (resolvedFairRetainedFrontSize s0 keep cap c),
      (∀ p < c, oneGapEdge (resolvedFairEventEdge s0) p
        (resolvedFairRetainedFront s0 keep cap c i) =
        oneGapEdge (resolvedFairEventEdge s0) p
        (resolvedFairRetainedFront s0 keep cap c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep cap c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep cap c j) := by
  dsimp only
  let keep := resolvedFairFiniteKeep s0 S auxKeep
  let cap := resolvedFairSelectionCap S
  let N := resolvedFairRetainedSize s0 cap
  let V := resolvedFairRetainedPool s0 keep cap
  let target := resolvedFairSelectedFrontIndex s0 hEmpty (resolvedFairSelectionWithCap S)
    auxKeep N V (resolvedFairOriginalAddress s0 n)
  have hTarget : ∀ i, n < target i :=
    resolvedFairSelectedFrontIndex_later s0 hEmpty (resolvedFairSelectionWithCap S)
      auxKeep N V n
  have hAddress : ∀ i, resolvedFairRetainedFront s0 keep cap
      (resolvedFairOriginalAddress s0 n) i = resolvedFairOriginalAddress s0 (target i) :=
    resolvedFairSelectedFrontIndex_address s0 hEmpty (resolvedFairSelectionWithCap S)
      auxKeep N V (resolvedFairOriginalAddress s0 n)
  intro i j hOld
  rw [hAddress i,hAddress j] at hOld ⊢
  exact resolvedFairOriginalCoding_no_split s0 hEmpty n (target i) (target j)
    (hTarget i) (hTarget j) hOld

theorem resolvedFairFiniteFront_code_age_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) (n : Nat) :
    let keep := resolvedFairFiniteKeep s0 S auxKeep
    let cap := resolvedFairSelectionCap S
    let c := resolvedFairOriginalAddress s0 n
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
      (resolvedFairRetainedFront s0 keep cap c) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
      (resolvedFairRetainedFront s0 keep cap c) := by
  dsimp only
  let keep := resolvedFairFiniteKeep s0 S auxKeep
  let cap := resolvedFairSelectionCap S
  let N := resolvedFairRetainedSize s0 cap
  let V := resolvedFairRetainedPool s0 keep cap
  let target := resolvedFairSelectedFrontIndex s0 hEmpty (resolvedFairSelectionWithCap S)
    auxKeep N V (resolvedFairOriginalAddress s0 n)
  have hTarget : ∀ i, n < target i :=
    resolvedFairSelectedFrontIndex_later s0 hEmpty (resolvedFairSelectionWithCap S)
      auxKeep N V n
  have hAddress : resolvedFairRetainedFront s0 keep cap (resolvedFairOriginalAddress s0 n) =
      fun i => resolvedFairOriginalAddress s0 (target i) := by
    funext i
    exact resolvedFairSelectedFrontIndex_address s0 hEmpty (resolvedFairSelectionWithCap S)
      auxKeep N V (resolvedFairOriginalAddress s0 n) i
  rw [hAddress]
  exact resolvedFairOriginalCoding_targetAge_neutral s0 hEmpty n target hTarget

theorem resolvedFairCriticalFront_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hc : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (ho : c ∉ resolvedFairRetainedLevels s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S)) (hr : oneGapReal c) :
    let keep := resolvedFairCriticalKeep s0 S
    let cap := resolvedFairSelectionCap S
    ∀ i j : Fin (resolvedFairRetainedFrontSize s0 keep cap c),
      (∀ p < c, oneGapEdge (resolvedFairEventEdge s0) p
        (resolvedFairRetainedFront s0 keep cap c i) =
        oneGapEdge (resolvedFairEventEdge s0) p
        (resolvedFairRetainedFront s0 keep cap c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep cap c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep cap c j) := by
  rcases resolvedFairCriticalCut_code_or_neutral s0 hEmpty S c hc ho hr with
    ⟨n,rfl⟩ | hRank
  · exact resolvedFairFiniteFront_code_no_split s0 hEmpty S (resolvedFairCriticalAuxKeep s0 S) n
  · dsimp only
    intro i j hOld
    exact fixedCritical_no_split (oneGapEdge (resolvedFairEventEdge s0))
      (resolvedFairFixedTerminals s0 S) c _ _
      (resolvedFairRetainedFront_mem_fixed s0 hEmpty S (resolvedFairCriticalAuxKeep s0 S) c i)
      (resolvedFairRetainedFront_mem_fixed s0 hEmpty S (resolvedFairCriticalAuxKeep s0 S) c j)
      hRank hOld

theorem resolvedFairCriticalFront_age_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hc : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (ho : c ∉ resolvedFairRetainedLevels s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S)) (hr : oneGapReal c) :
    let keep := resolvedFairCriticalKeep s0 S
    let cap := resolvedFairSelectionCap S
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
      (resolvedFairRetainedFront s0 keep cap c) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
      (resolvedFairRetainedFront s0 keep cap c) := by
  rcases resolvedFairCriticalCut_code_or_neutral s0 hEmpty S c hc ho hr with
    ⟨n,rfl⟩ | hRank
  · exact resolvedFairFiniteFront_code_age_neutral s0 hEmpty S (resolvedFairCriticalAuxKeep s0 S) n
  · dsimp only
    unfold resolvedTargetAge
    have hRaw := fixedCritical_raw_neutral (oneGapEdge (resolvedFairEventEdge s0))
      (resolvedFairFixedTerminals s0 S)
      (resolvedFairRetainedFront s0 (resolvedFairCriticalKeep s0 S)
        (resolvedFairSelectionCap S) c)
      (fun i => resolvedFairRetainedFront_mem_fixed s0 hEmpty S
        (resolvedFairCriticalAuxKeep s0 S) c i) c hRank
    exact congrArg (integerGraphAgeCanonical
      (resolvedFairRetainedFrontSize s0 (resolvedFairCriticalKeep s0 S)
        (resolvedFairSelectionCap S) c) 4) hRaw

/-- Every certified event has at most three ordinary vertices. -/
theorem ResolvedEventCertificate.block_length_le_three {W : Set Nat}
    {r : Nat} {e : ResolvedEvent} (h : ResolvedEventCertificate W r e) :
    e.block.length ≤ 3 := by
  cases h with
  | marker => simp
  | cover s Q T hPQ hQW hBudget hCover hChanged hMinimal hSize =>
      simpa only [Finset.length_sort] using (show Q.card ≤ 3 by omega)
  | code => simp

theorem resolvedFairEventBlock_length_le_three
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (k : Nat) :
    (resolvedFairEventBlock s0 k).length ≤ 3 :=
  (resolvedFairEvent_certificate s0 k).block_length_le_three

noncomputable def resolvedFairBoundedEvents
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) : Finset Nat :=
  (resolvedFairSelectionWithCap S).image (resolvedFairCodingEvent s0) ∪
    resolvedFairCriticalEvents s0 S

def resolvedFairRetentionBudget (m : Nat) : Nat := m + m*m + 2^m*3

theorem resolvedFairBoundedEvents_card_le
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) :
    (resolvedFairBoundedEvents s0 S).card ≤ resolvedFairRetentionBudget (S.card+1) := by
  classical
  have hCritical : (resolvedFairCriticalEvents s0 S).card ≤
      (S.card+1)*(S.card+1) + 2^(S.card+1)*3 := by
    unfold resolvedFairCriticalEvents
    have h := fixedCriticalCuts_card_le (oneGapEdge (resolvedFairEventEdge s0))
      (resolvedFairFixedTerminals s0 S)
      (resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    rw [resolvedFairFixedTerminals_card] at h
    exact Finset.card_image_le.trans h
  have hCode : ((resolvedFairSelectionWithCap S).image
      (resolvedFairCodingEvent s0)).card ≤ S.card+1 :=
    Finset.card_image_le.trans_eq (resolvedFairSelectionWithCap_card S)
  unfold resolvedFairBoundedEvents resolvedFairRetentionBudget
  have hUnion := Finset.card_union_le
    ((resolvedFairSelectionWithCap S).image (resolvedFairCodingEvent s0))
    (resolvedFairCriticalEvents s0 S)
  omega

theorem resolvedFairCriticalKeep_mem_events
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) (k : Nat)
    (hk : resolvedFairCriticalKeep s0 S k = true) :
    k ∈ resolvedFairBoundedEvents s0 S := by
  classical
  change (if (resolvedFairEvent s0 k).kind = .code then
    decide (k ∈ (resolvedFairSelectionWithCap S).image (resolvedFairCodingEvent s0))
    else resolvedFairCriticalAuxKeep s0 S k) = true at hk
  by_cases hCode : (resolvedFairEvent s0 k).kind = .code
  · rw [if_pos hCode, decide_eq_true_eq] at hk
    exact Finset.mem_union.mpr (Or.inl hk)
  · rw [if_neg hCode] at hk
    exact Finset.mem_union.mpr (Or.inr (of_decide_eq_true hk))

/-- Count vertex positions by event occurrence and offset in that event.
Counting critical cuts alone would not count all vertices in kept blocks. -/
theorem resolvedFairCriticalPositions_card_le
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) :
    (resolvedFairRetainedPositions s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S)).card ≤
      resolvedFairRetentionBudget (S.card+1) * 3 := by
  classical
  let P := resolvedFairRetainedPositions s0 (resolvedFairCriticalKeep s0 S)
    (resolvedFairSelectionCap S)
  let B := resolvedFairBoundedEvents s0 S
  let size := fun k => (resolvedFairEventBlock s0 k).length
  let f := fun p : Nat => (resolvedFairVertexEventIndex s0 p,
    p - oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 p))
  have hLower (p : Nat) : oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 p) ≤ p :=
    (oneGapBatchIndex_bounds size (resolvedFairEventBlock_positive s0) p).1
  have hOffset (p : Nat) : (f p).2 < 3 := by
    have hb := (oneGapBatchIndex_bounds size (resolvedFairEventBlock_positive s0) p).2
    change p < oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 p + 1) at hb
    rw [oneGapBatchBoundary_succ] at hb
    have hLen : size (resolvedFairVertexEventIndex s0 p) ≤ 3 :=
      resolvedFairEventBlock_length_le_three s0 _
    change p - oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 p) < 3
    omega
  have hMaps : Set.MapsTo f (P : Set Nat) (B.product (Finset.range 3) : Set (Nat × Nat)) := by
    intro p hp
    change p ∈ P at hp
    change f p ∈ B.product (Finset.range 3)
    apply Finset.mem_product.mpr
    refine ⟨resolvedFairCriticalKeep_mem_events s0 S _
      ((resolvedFairRetainedPositions_mem_iff s0 (resolvedFairCriticalKeep s0 S)
        (resolvedFairSelectionCap S) p).mp hp).2,
      Finset.mem_range.mpr (hOffset p)⟩
  have hInj : Set.InjOn f (P : Set Nat) := by
    intro p _ q _ hEq
    have hEvent := congrArg Prod.fst hEq
    have hOff := congrArg Prod.snd hEq
    change resolvedFairVertexEventIndex s0 p = resolvedFairVertexEventIndex s0 q at hEvent
    change p - oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 p) =
      q - oneGapBatchBoundary size (resolvedFairVertexEventIndex s0 q) at hOff
    have hp := hLower p
    have hq := hLower q
    rw [hEvent] at hp hOff
    omega
  calc
    P.card ≤ (B.product (Finset.range 3)).card :=
      Finset.card_le_card_of_injOn f hMaps hInj
    _ = B.card * 3 := by simp [Finset.card_product]
    _ ≤ resolvedFairRetentionBudget (S.card+1)*3 :=
      Nat.mul_le_mul_right 3 (resolvedFairBoundedEvents_card_le s0 S)

/-- Anchor plus a gap/vertex pair for every retained ordinary position. -/
theorem oneGapPairedLevels_card_le_twice (P : Finset Nat) :
    (oneGapPairedLevels P).card ≤ 2*P.card+1 := by
  classical
  unfold oneGapPairedLevels
  have hInsert := Finset.card_insert_le 0
    ((P.image (fun i => 2*i+1)) ∪ P.image oneGapAddress)
  have hUnion := Finset.card_union_le (P.image (fun i => 2*i+1)) (P.image oneGapAddress)
  have hGap : (P.image (fun i => 2*i+1)).card ≤ P.card := Finset.card_image_le
  have hReal : (P.image oneGapAddress).card ≤ P.card := Finset.card_image_le
  omega

theorem resolvedFairCriticalLevels_card_le
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (S : Finset Nat) :
    (resolvedFairRetainedLevels s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S)).card ≤ 6*resolvedFairRetentionBudget (S.card+1)+1 := by
  have hp := resolvedFairCriticalPositions_card_le s0 S
  have hPair := oneGapPairedLevels_card_le_twice
    (resolvedFairRetainedPositions s0 (resolvedFairCriticalKeep s0 S)
      (resolvedFairSelectionCap S))
  change (resolvedFairRetainedLevels s0 (resolvedFairCriticalKeep s0 S)
    (resolvedFairSelectionCap S)).card ≤ _ at hPair
  omega

/-- Uniformly bounded actual envelopes for the original selection plus
cap. The full original seed set and all ordinary premises are derived. -/
theorem resolvedFairCriticalFiniteSelection_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) :
    let keep := resolvedFairCriticalKeep s0 S
    let n := resolvedFairSelectionCap S
    (resolvedFairRetainedLevels s0 keep n).card ≤ 6*resolvedFairRetentionBudget (S.card+1)+1 ∧
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        (resolvedFairFiniteOriginalSeeds s0 hEmpty S) (resolvedFairRetainedTop s0 n) 0
        (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  dsimp only
  refine ⟨resolvedFairCriticalLevels_card_le s0 S, ?_⟩
  let n := resolvedFairSelectionCap S
  let U := resolvedFairFiniteOriginalPool s0 S
  let aux := resolvedFairCriticalAuxKeep s0 S
  let keep := resolvedFairCriticalKeep s0 S
  have hUV : U ⊆ resolvedFairRetainedPool s0 keep n :=
    resolvedFairFiniteOriginalPool_retained s0 S aux
  exact resolvedFairFiniteSelection_envelope s0 hEmpty S aux
    (resolvedFairFiniteOriginalSeeds s0 hEmpty S)
    (resolvedFairOriginalSeeds_bounded s0 hEmpty n U) U
    (resolvedFairOriginalSeeds_pool s0 hEmpty n U) hUV
    (resolvedFairOriginalSeeds_retained s0 hEmpty keep n U hUV)
    (resolvedFairCriticalFront_no_split s0 hEmpty S)
    (fun c hc ho hr T => congrFun (resolvedFairCriticalFront_age_neutral s0 hEmpty S c hc ho hr) T)

theorem resolvedInitialCriticalFiniteSelection_envelope
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (S : Finset Nat) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    let keep := resolvedFairCriticalKeep s0 S
    let n := resolvedFairSelectionCap S
    (resolvedFairRetainedLevels s0 keep n).card ≤ 6*resolvedFairRetentionBudget (S.card+1)+1 ∧
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        (resolvedFairFiniteOriginalSeeds s0 rfl S) (resolvedFairRetainedTop s0 n) 0
        (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  dsimp only
  exact resolvedFairCriticalFiniteSelection_envelope (resolvedInitialStage E hFree hSym hLoops) rfl S

end Kk
