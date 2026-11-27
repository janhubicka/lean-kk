import Kk.ResolvedFairAuxiliarySelection
import Kk.ResolvedFairOriginalSeeds
import Kk.ResolvedFairCodingNeutrality

/-!
# Actual finite envelopes with every auxiliary event retained

English proof reviewed before implementation:
`docs/all_auxiliary_envelope_english_20261127.md`.
Actual coding certificates and exact chronological/padded age transport
derive the ordinary hypotheses. Full original seeds supply all pool and
retained-seed data. No complete diary-record bound is asserted.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

/-- The actual coding no-split theorem at the padded original addresses. -/
theorem resolvedFairOriginalCoding_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (n v w : Nat) (hv : n < v) (hw : n < w)
    (hOld : ∀ q, q < resolvedFairOriginalAddress s0 n →
      oneGapEdge (resolvedFairEventEdge s0) q (resolvedFairOriginalAddress s0 v) =
        oneGapEdge (resolvedFairEventEdge s0) q (resolvedFairOriginalAddress s0 w)) :
    oneGapEdge (resolvedFairEventEdge s0) (resolvedFairOriginalAddress s0 n)
        (resolvedFairOriginalAddress s0 v) =
      oneGapEdge (resolvedFairEventEdge s0) (resolvedFairOriginalAddress s0 n)
        (resolvedFairOriginalAddress s0 w) := by
  have hRaw := (oneGap_oldColumns_before_iff (resolvedFairEventEdge s0)
    (resolvedFairEventCodePosition s0 n) (resolvedFairEventCodePosition s0 v)
    (resolvedFairEventCodePosition s0 w)).mp hOld
  simpa only [resolvedFairOriginalAddress, oneGapEdge_address] using
    resolvedFairEventCoding_no_split s0 hEmpty n v w hv hw hRaw

/-- Full canonical selected-age neutrality at a padded actual coding cut. -/
theorem resolvedFairOriginalCoding_targetAge_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    {d : Nat} (n : Nat) (target : Fin d → Nat) (hTarget : ∀ i, n < target i) :
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4
      (Finset.range (resolvedFairOriginalAddress s0 n))
      (fun i => resolvedFairOriginalAddress s0 (target i)) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4
      (Finset.range (resolvedFairOriginalAddress s0 n + 1))
      (fun i => resolvedFairOriginalAddress s0 (target i)) :=
  oneGap_canonicalAge_neutral_of_unpadded (resolvedFairEventEdge s0) 4 d
    (resolvedFairEventCodePosition s0 n)
    (fun i => resolvedFairEventCodePosition s0 (target i))
    (resolvedFairEventCoding_targetAge_neutral s0 hEmpty n target hTarget)

/-- No split for the actual finite front at each omitted meaningful cut. -/
theorem resolvedFairAllAuxRetainedFront_no_split
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hCut : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (hOmitted : c ∉ resolvedFairRetainedLevels s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S))
    (hReal : oneGapReal c) :
    ∀ i j : Fin (resolvedFairRetainedFrontSize s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S) c),
      (∀ p, p < c → oneGapEdge (resolvedFairEventEdge s0) p
          (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
            (resolvedFairSelectionCap S) c i) =
        oneGapEdge (resolvedFairEventEdge s0) p
          (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
            (resolvedFairSelectionCap S) c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c
          (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
            (resolvedFairSelectionCap S) c i) =
        oneGapEdge (resolvedFairEventEdge s0) c
          (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
            (resolvedFairSelectionCap S) c j) := by
  obtain ⟨n, _hn, rfl⟩ := resolvedFairAllAux_omitted_real s0 hEmpty S c hCut hOmitted hReal
  let keep := resolvedFairFiniteKeep s0 S (fun _ => true)
  let cap := resolvedFairSelectionCap S
  let N := resolvedFairRetainedSize s0 cap
  let V := resolvedFairRetainedPool s0 keep cap
  let target := resolvedFairSelectedFrontIndex s0 hEmpty (resolvedFairSelectionWithCap S)
    (fun _ => true) N V (resolvedFairOriginalAddress s0 n)
  have hTarget : ∀ i, n < target i :=
    resolvedFairSelectedFrontIndex_later s0 hEmpty (resolvedFairSelectionWithCap S)
      (fun _ => true) N V n
  have hAddress : ∀ i, resolvedFairRetainedFront s0 keep cap
      (resolvedFairOriginalAddress s0 n) i = resolvedFairOriginalAddress s0 (target i) :=
    resolvedFairSelectedFrontIndex_address s0 hEmpty (resolvedFairSelectionWithCap S)
      (fun _ => true) N V (resolvedFairOriginalAddress s0 n)
  intro i j hOld
  rw [hAddress i, hAddress j] at hOld ⊢
  exact resolvedFairOriginalCoding_no_split s0 hEmpty n (target i) (target j)
    (hTarget i) (hTarget j) hOld

/-- The complete canonical age of the actual finite front is unchanged. -/
theorem resolvedFairAllAuxRetainedFront_targetAge_neutral
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (c : Nat)
    (hCut : c < resolvedFairRetainedTop s0 (resolvedFairSelectionCap S))
    (hOmitted : c ∉ resolvedFairRetainedLevels s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S))
    (hReal : oneGapReal c) :
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range c)
      (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
        (resolvedFairSelectionCap S) c) =
    resolvedTargetAge (oneGapEdge (resolvedFairEventEdge s0)) 4 (Finset.range (c+1))
      (resolvedFairRetainedFront s0 (resolvedFairFiniteKeep s0 S (fun _ => true))
        (resolvedFairSelectionCap S) c) := by
  obtain ⟨n, _hn, rfl⟩ := resolvedFairAllAux_omitted_real s0 hEmpty S c hCut hOmitted hReal
  let keep := resolvedFairFiniteKeep s0 S (fun _ => true)
  let cap := resolvedFairSelectionCap S
  let N := resolvedFairRetainedSize s0 cap
  let V := resolvedFairRetainedPool s0 keep cap
  let target := resolvedFairSelectedFrontIndex s0 hEmpty (resolvedFairSelectionWithCap S)
    (fun _ => true) N V (resolvedFairOriginalAddress s0 n)
  have hTarget : ∀ i, n < target i :=
    resolvedFairSelectedFrontIndex_later s0 hEmpty (resolvedFairSelectionWithCap S)
      (fun _ => true) N V n
  have hAddress : resolvedFairRetainedFront s0 keep cap (resolvedFairOriginalAddress s0 n) =
      fun i => resolvedFairOriginalAddress s0 (target i) := by
    funext i
    exact resolvedFairSelectedFrontIndex_address s0 hEmpty (resolvedFairSelectionWithCap S)
      (fun _ => true) N V (resolvedFairOriginalAddress s0 n) i
  rw [hAddress]
  exact resolvedFairOriginalCoding_targetAge_neutral s0 hEmpty n target hTarget

/-- All age/no-split and seed conditions are derived for full original
seeds of any subpool of the constructed retained pool. -/
theorem resolvedFairAllAuxOriginalSeeds_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat)
    (U : Set (Fin (resolvedFairRetainedSize s0 (resolvedFairSelectionCap S))))
    (hUV : U ⊆ resolvedFairRetainedPool s0
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S)) :
    let keep := resolvedFairFiniteKeep s0 S (fun _ => true)
    let n := resolvedFairSelectionCap S
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        (resolvedFairOriginalSeeds s0 hEmpty n U) (resolvedFairRetainedTop s0 n) 0
        (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  dsimp only
  exact resolvedFairFiniteSelection_envelope s0 hEmpty S (fun _ => true)
    (resolvedFairOriginalSeeds s0 hEmpty (resolvedFairSelectionCap S) U)
    (resolvedFairOriginalSeeds_bounded s0 hEmpty (resolvedFairSelectionCap S) U) U
    (resolvedFairOriginalSeeds_pool s0 hEmpty (resolvedFairSelectionCap S) U) hUV
    (resolvedFairOriginalSeeds_retained s0 hEmpty
      (resolvedFairFiniteKeep s0 S (fun _ => true)) (resolvedFairSelectionCap S) U hUV)
    (resolvedFairAllAuxRetainedFront_no_split s0 hEmpty S)
    (fun c hc ho hr T => congrFun
      (resolvedFairAllAuxRetainedFront_targetAge_neutral s0 hEmpty S c hc ho hr) T)

/-- The selected originals and fresh cap have an actual full envelope;
no age, no-split, seed-coverage or cap-choice hypotheses remain. -/
theorem resolvedFairAllAuxFiniteSelection_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) :
    let keep := resolvedFairFiniteKeep s0 S (fun _ => true)
    let n := resolvedFairSelectionCap S
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        (resolvedFairFiniteOriginalSeeds s0 hEmpty S) (resolvedFairRetainedTop s0 n) 0
        (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} :=
  resolvedFairAllAuxOriginalSeeds_envelope s0 hEmpty S (resolvedFairFiniteOriginalPool s0 S)
    (resolvedFairFiniteOriginalPool_retained s0 S (fun _ => true))

/-- Start directly from a symmetric loopless K4-free ordinary graph.
The initial stage, its empty old pool and all finite envelope data are supplied. -/
theorem resolvedInitialAllAuxFiniteSelection_envelope
    (E : Nat → Nat → Bool)
    (hFree : ∀ C : Finset Nat, IsDirectedCliqueOn E C → C.card < 4)
    (hSym : ∀ x y, E x y = E y x) (hLoops : ∀ x, E x x = false)
    (S : Finset Nat) :
    let s0 := resolvedInitialStage E hFree hSym hLoops
    let keep := resolvedFairFiniteKeep s0 S (fun _ => true)
    let n := resolvedFairSelectionCap S
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        (resolvedFairFiniteOriginalSeeds s0 rfl S) (resolvedFairRetainedTop s0 n) 0
        (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  dsimp only
  exact resolvedFairAllAuxFiniteSelection_envelope
    (resolvedInitialStage E hFree hSym hLoops) rfl S

end Kk
