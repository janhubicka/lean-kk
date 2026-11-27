import Kk.ResolvedFairSelectedFront
import Kk.ResolvedFairRetainedPlan
import Kk.ResolvedFairFiniteSelection
import Kk.ResolvedFairOneGap

/-!
# An actual retained plan and constructed-front envelope

English proof and independent pre-code review:
`docs/finite_selected_front_english_20261127.md`.
The finite retained levels, complete pool and selected fronts are
constructed. The remaining selected-age and no-split obligations are
explicit; no diary parser or common inverse source is asserted.
-/

namespace Kk
open SuccessorTree
open SuccessorTree.V10
open SuccessorTree.SMTree.Envelope

noncomputable def resolvedFairRetainedFrontSize
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n cut : Nat) : Nat :=
  resolvedFairSelectedFrontSize s0 keep (resolvedFairRetainedSize s0 n)
    (resolvedFairRetainedPool s0 keep n) cut

noncomputable def resolvedFairRetainedFront
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n cut : Nat) : Fin (resolvedFairRetainedFrontSize s0 keep n cut) → Nat :=
  resolvedFairSelectedFront s0 keep (resolvedFairRetainedSize s0 n)
    (resolvedFairRetainedPool s0 keep n) cut

/-- At every omitted cut below the cap, its retained preceding gap makes
the cap eligible. Mere strict inequality with the cap would not suffice. -/
theorem resolvedFairRetainedCap_eligible_of_omitted
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true)
    (cut : Nat) (hCut : cut < resolvedFairRetainedTop s0 n)
    (hOmitted : cut ∉ resolvedFairRetainedLevels s0 keep n) :
    cut+1 ≤ ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel (resolvedFairRetainedTop s0 n) := by
  rw [oneGapPartial_freeLevel _ _ _ (resolvedFairRetainedTop_lt_size s0 n),
    ite_eq_left (show oneGapReal (resolvedFairRetainedTop s0 n) from oneGapAddress_real _)]
  have hGap := resolvedFairRetainedLevels_cap_gap s0 keep n hCap
  have hNe : cut ≠ resolvedFairRetainedTop s0 n - 1 := by
    intro hEq
    exact hOmitted (hEq.symm ▸ hGap)
  omega

/-- The actual coded cap occurs in every omitted-cut front, including
omitted dummy cuts. It is never put into an unproved old-zero class. -/
theorem resolvedFairRetainedFront_cap
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true)
    (cut : Nat) (hCut : cut < resolvedFairRetainedTop s0 n)
    (hOmitted : cut ∉ resolvedFairRetainedLevels s0 keep n) :
    ∃ i, resolvedFairRetainedTop s0 n = resolvedFairRetainedFront s0 keep n cut i := by
  apply (resolvedFairSelectedFront_range s0 keep (resolvedFairRetainedSize s0 n)
    (resolvedFairRetainedPool s0 keep n) cut (resolvedFairRetainedCap s0 n)).mpr
  refine ⟨resolvedFairRetainedCap_mem s0 keep n hCap,
    resolvedFairRetainedCap_eligible_of_omitted s0 keep n hCap cut hCut hOmitted, ?_⟩
  have hRole := resolvedFairEventRole_originalAddress s0 keep n
  simpa only [resolvedFairRetainedCap, resolvedFairRetainedTop,
    resolvedFairOriginalAddress, hCap] using hRole

theorem resolvedFairRetainedFrontSize_pos_of_omitted
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (keep : Nat → Bool)
    (n : Nat) (hCap : keep (resolvedFairCodingEvent s0 n) = true)
    (cut : Nat) (hCut : cut < resolvedFairRetainedTop s0 n)
    (hOmitted : cut ∉ resolvedFairRetainedLevels s0 keep n) :
    0 < resolvedFairRetainedFrontSize s0 keep n cut := by
  obtain ⟨i, _hi⟩ := resolvedFairRetainedFront_cap s0 keep n hCap cut hCut hOmitted
  exact Nat.zero_lt_of_lt i.isLt

theorem resolvedFairRetainedFront_positive
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n cut : Nat)
    (hCut : cut < resolvedFairRetainedTop s0 n)
    (hOmitted : cut ∉ resolvedFairRetainedLevels s0 keep n)
    (hReal : oneGapReal cut)
    (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v ∈ resolvedFairRetainedPool s0 keep n)
    (hEligible : cut+1 ≤ ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel v.val)
    (hEdge : oneGapEdge (resolvedFairEventEdge s0) cut v.val = true) :
    ∃ i, v.val = resolvedFairRetainedFront s0 keep n cut i :=
  resolvedFairSelectedFront_positive s0 hEmpty keep (resolvedFairRetainedSize s0 n)
    (resolvedFairRetainedPool s0 keep n) (fun _ hv => hv) cut
    (resolvedFairRetainedLevels_omitted_real_not_retained s0 keep n cut hCut hOmitted hReal)
    v hv hEligible hEdge

theorem resolvedFairRetainedFront_other_zero
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n cut : Nat)
    (hCut : cut < resolvedFairRetainedTop s0 n)
    (hOmitted : cut ∉ resolvedFairRetainedLevels s0 keep n)
    (hReal : oneGapReal cut)
    (v : Fin (resolvedFairRetainedSize s0 n))
    (hv : v ∈ resolvedFairRetainedPool s0 keep n)
    (hEligible : cut+1 ≤ ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix
      (resolvedFairRetainedSize s0 n)).freeLevel v.val)
    (hNotSelected : ¬ ∃ i, v.val = resolvedFairRetainedFront s0 keep n cut i) :
    ∀ p, p < cut → oneGapEdge (resolvedFairEventEdge s0) p v.val = false :=
  resolvedFairSelectedFront_other_zero s0 hEmpty keep (resolvedFairRetainedSize s0 n)
    (resolvedFairRetainedPool s0 keep n) (fun _ hv => hv) cut
    (resolvedFairRetainedLevels_omitted_real_not_retained s0 keep n cut hCut hOmitted hReal)
    v hv hEligible hNotSelected

theorem resolvedFairEventGraph_avoids
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅) :
    ∀ bad, bad ∈ hensonForbiddenFamily 4 (by omega) →
      bad.Avoids (normalizedGraphModel (resolvedFairEventEdge s0)) :=
  henson_avoids_of_finite_clique_bound (resolvedFairEventEdge s0)
    4 (by omega) (resolvedFairEventEdge_free s0 hEmpty)
    (resolvedFairEventEdge_sym s0) (resolvedFairEventEdge_loops s0)

/-- The actual graph, finite retained plan, complete pool, selected lists,
cap and both graph premises are constructed. Selected age/no-split and
seed/pool application data remain explicit inputs. -/
theorem resolvedFairRetained_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (keep : Nat → Bool) (n : Nat)
    (hCap : keep (resolvedFairCodingEvent s0 n) = true)
    (X : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (by omega))))
    (hXBound : X ⊆ levelLe (resolvedFairRetainedTop s0 n))
    (U : Set (Fin (resolvedFairRetainedSize s0 n)))
    (hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily 4 (by omega))
      ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix (resolvedFairRetainedSize s0 n))
      (oneGap_finitePrefix_avoids (resolvedFairEventEdge s0) 4 (by omega)
        (resolvedFairEventGraph_avoids s0 hEmpty) (resolvedFairRetainedSize s0 n)) U)
    (hUV : U ⊆ resolvedFairRetainedPool s0 keep n)
    (hSeedRet : ∀ z ∈ X, LevelTree.lev z ∈ resolvedFairRetainedLevels s0 keep n)
    (hNoSplit : ∀ c, c < resolvedFairRetainedTop s0 n →
      c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
      ∀ i j : Fin (resolvedFairRetainedFrontSize s0 keep n c),
      (∀ p < c, oneGapEdge (resolvedFairEventEdge s0) p (resolvedFairRetainedFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) p (resolvedFairRetainedFront s0 keep n c j)) →
      oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep n c i) =
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep n c j))
    (hAge : ∀ c, c < resolvedFairRetainedTop s0 n →
      c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
      ∀ T : IntegerGraphSupport (resolvedFairRetainedFrontSize s0 keep n c) 4,
      integerGraphAgeCanonical (resolvedFairRetainedFrontSize s0 keep n c) 4
        (finiteOldColumnRawBound (oneGapEdge (resolvedFairEventEdge s0)) 4
          (resolvedFairRetainedFrontSize s0 keep n c) (Finset.range c)
          (fun p j => oneGapEdge (resolvedFairEventEdge s0) p
            (resolvedFairRetainedFront s0 keep n c j))) T =
      integerGraphAgeCanonical (resolvedFairRetainedFrontSize s0 keep n c) 4
        (finiteOldColumnRawBound (oneGapEdge (resolvedFairEventEdge s0)) 4
          (resolvedFairRetainedFrontSize s0 keep n c) (Finset.range (c+1))
          (fun p j => oneGapEdge (resolvedFairEventEdge s0) p
            (resolvedFairRetainedFront s0 keep n c j))) T) :
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        X (resolvedFairRetainedTop s0 n) 0 (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  exact oneGap_planned_envelope_of_real_selected_neutrality
    (resolvedFairEventEdge s0) 4 (by omega) (resolvedFairEventGraph_avoids s0 hEmpty)
    (resolvedFairRetainedSize s0 n) X (resolvedFairRetainedTop s0 n)
    (resolvedFairRetainedTop_lt_size s0 n) hXBound
    (resolvedFairRetainedLevels s0 keep n : Set Nat)
    (resolvedFairRetainedLevels_zero s0 keep n)
    (resolvedFairRetainedLevels_top s0 keep n hCap)
    (resolvedFairRetainedLevels_bound s0 keep n) U (resolvedFairRetainedPool s0 keep n)
    hX hUV (resolvedFairRetainedPool_retained_parameters s0 keep n) hSeedRet
    (resolvedFairRetainedPool_pair_retention s0 keep n)
    (resolvedFairRetainedFrontSize s0 keep n) (resolvedFairRetainedFront s0 keep n)
    (resolvedFairRetainedFront_positive s0 hEmpty keep n)
    (fun c hc ho hr i j _hi _hj hOld => hNoSplit c hc ho hr i j hOld)
    (resolvedFairRetainedFront_other_zero s0 hEmpty keep n) hAge

/-- Start with any finite original selection, including the empty set.
The fresh coded cap, its keep flag, actual prefix, retained pool/levels,
and selected lists are all supplied by the construction. The remaining
seed/pool and ordinary age/no-split inputs are stated in full. -/
theorem resolvedFairFiniteSelection_envelope
    (s0 : ResolvedBareStage 4 (resolvedEvenTail 0)) (hEmpty : s0.old = ∅)
    (S : Finset Nat) (auxKeep : Nat → Bool) :
    let keep := resolvedFairFiniteKeep s0 S auxKeep
    let n := resolvedFairSelectionCap S
    ∀ (X : Set (AdmissibleKptNode (hensonForbiddenFamily 4 (by omega))))
      (_hXBound : X ⊆ levelLe (resolvedFairRetainedTop s0 n))
      (U : Set (Fin (resolvedFairRetainedSize s0 n)))
      (_hX : X ⊆ ambientPrefixPool (hensonForbiddenFamily 4 (by omega))
        ((oneGapPartial (resolvedFairEventEdge s0)).finitePrefix (resolvedFairRetainedSize s0 n))
        (oneGap_finitePrefix_avoids (resolvedFairEventEdge s0) 4 (by omega)
          (resolvedFairEventGraph_avoids s0 hEmpty) (resolvedFairRetainedSize s0 n)) U)
      (_hUV : U ⊆ resolvedFairRetainedPool s0 keep n)
      (_hSeedRet : ∀ z ∈ X, LevelTree.lev z ∈ resolvedFairRetainedLevels s0 keep n)
      (_hNoSplit : ∀ c, c < resolvedFairRetainedTop s0 n →
        c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
        ∀ i j : Fin (resolvedFairRetainedFrontSize s0 keep n c),
        (∀ p < c, oneGapEdge (resolvedFairEventEdge s0) p (resolvedFairRetainedFront s0 keep n c i) =
          oneGapEdge (resolvedFairEventEdge s0) p (resolvedFairRetainedFront s0 keep n c j)) →
        oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep n c i) =
          oneGapEdge (resolvedFairEventEdge s0) c (resolvedFairRetainedFront s0 keep n c j))
      (_hAge : ∀ c, c < resolvedFairRetainedTop s0 n →
        c ∉ resolvedFairRetainedLevels s0 keep n → oneGapReal c →
        ∀ T : IntegerGraphSupport (resolvedFairRetainedFrontSize s0 keep n c) 4,
        integerGraphAgeCanonical (resolvedFairRetainedFrontSize s0 keep n c) 4
          (finiteOldColumnRawBound (oneGapEdge (resolvedFairEventEdge s0)) 4
            (resolvedFairRetainedFrontSize s0 keep n c) (Finset.range c)
            (fun p j => oneGapEdge (resolvedFairEventEdge s0) p
              (resolvedFairRetainedFront s0 keep n c j))) T =
        integerGraphAgeCanonical (resolvedFairRetainedFrontSize s0 keep n c) 4
          (finiteOldColumnRawBound (oneGapEdge (resolvedFairEventEdge s0)) 4
            (resolvedFairRetainedFrontSize s0 keep n c) (Finset.range (c+1))
            (fun p j => oneGapEdge (resolvedFairEventEdge s0) p
              (resolvedFairRetainedFront s0 keep n c j))) T),
    ∃ F : SMTree.MMap (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega))),
      StageFullInvariant (normalizedKptSMTree (hensonForbiddenFamily 4 (by omega)))
        X (resolvedFairRetainedTop s0 n) 0 (resolvedFairRetainedLevels s0 keep n : Set Nat) F ∧
      F.map.levelRange = {q | q ∈ resolvedFairRetainedLevels s0 keep n ∨
        resolvedFairRetainedTop s0 n < q} := by
  dsimp only
  intro X hXBound U hX hUV hSeedRet hNoSplit hAge
  exact resolvedFairRetained_envelope s0 hEmpty
    (resolvedFairFiniteKeep s0 S auxKeep) (resolvedFairSelectionCap S)
    (resolvedFairFiniteKeep_cap s0 S auxKeep) X hXBound U hX hUV hSeedRet hNoSplit hAge

end Kk
