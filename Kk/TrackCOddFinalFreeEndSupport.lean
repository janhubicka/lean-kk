import Kk.TrackCChronologicalOddSourceQuiet
import Kk.TrackDPreCutStageSource
import Mathlib.Tactic

/-!
# Track C: a single finite final-physical-source exception set for ODD free ends

English-first hostile proof:
 docs/track_c_odd_final_freeend_finite_support_english_audit_20261121.md

For a GENUINE old normalized Kpt AlgorithmRun, the complete
pre-cut original source pool at c is a subset of the final
original pool at Rold.I 0. Hence ALL original E-free endpoints
which can occur at old-range source cuts lie in the image of
one fixed finite original pool. Its cardinal is at most M.

With the already VERIFIED chronological physical #441 odd-root
theorem, every old-unselected ODD cut outside this physically
CONSTRUCTED exceptional set is full candidate Kpt quiet as
soon as its COMPLETE original old-Kpt-prefix coverage holds.
No per-cut no-stage-free-end assumption remains.

This finite |F|<=M is NOT a diary-uniform BRD bound: M may grow.
The exceptional cuts and missing old-prefix witnesses remain
true geometric obstacles, as do even nonzero and K4 q2/E cuts.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The true original stage based on the selected levels above cut
is included in the final TRUE stage pool, for a GENUINE
AlgorithmRun. Arbitrary proposed level masks do not suffice. -/
theorem kpt_physical_stage_originals_subset_final
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (cut : Nat) (hCut : cut < oldTop) :
    hStageOriginals L k M W (Rold.I (cut+1)) ⊆
      hStageOriginals L k M W (Rold.I 0) := by
  have hLevels : Rold.I (cut+1) ⊆ Rold.I 0 := by
    intro q hq
    rw [Rold.I_eq_final_tail_of_run (cut+1) (by omega)] at hq
    exact hq.1
  intro v hv
  simp only [hStageOriginals, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.mem_ofPred_eq] at hv ⊢
  rcases hv with hRoot | ⟨hSelected,hPositive⟩
  · exact Or.inl hRoot
  · exact Or.inr ⟨hLevels hSelected,hPositive⟩

/-- The source-level endpoints of ALL original coordinates of
the actual FINAL physical stage. This is a Finset Nat, not an
axiomatically finite selected-graph-age support. -/
noncomputable def KptPhysicalFinalStageFreeEnds
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) : Finset Nat := by
  classical
  exact (hStageOriginals L k M W (Rold.I 0)).image
    (fun v : Fin M => (finiteNumericH L k M).freeLevel v.val)

/-- One finite numerical-H+ carrier M bounds the number of
DISTINCT potentially ending original-stage E-free source cuts.
This is a per-stage bound only, not a uniform Kk-free BRD. -/
theorem kpt_physical_final_freeend_cuts_card_le_carrier
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop) :
    (KptPhysicalFinalStageFreeEnds
      family L k M W X oldTop Rold).card ≤ M := by
  classical
  unfold KptPhysicalFinalStageFreeEnds
  calc
    ((hStageOriginals L k M W (Rold.I 0)).image
      (fun v : Fin M =>
        (finiteNumericH L k M).freeLevel v.val)).card ≤
        (hStageOriginals L k M W (Rold.I 0)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin M)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = M := by simp

/-- Outside the constructed final E-free endpoint set, NO
original of the actual pre-cut stage W∪positiveSelected(Rold.I(c+1))
can end at c. This holds for ANY c<oldTop, not just odd c.
The true old-run selected-tail identity is essential. -/
theorem kpt_physical_no_stage_free_end_outside_final
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (L : AgeTestModel db du dd) (k M : Nat)
    (W : Finset (Fin M))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (cut : Nat) (hCut : cut < oldTop)
    (hNotFinal :
      cut ∉ KptPhysicalFinalStageFreeEnds
        family L k M W X oldTop Rold) :
    ∀ v : Fin M,
      v ∈ ambientStagePool (finiteNumericH L k M)
        (W : Set (Fin M)) (Rold.I (cut+1)) →
      (finiteNumericH L k M).freeLevel v.val ≠ cut := by
  intro v hStage hEq
  have hvStage :
      v ∈ hStageOriginals L k M W (Rold.I (cut+1)) := by
    have hInput :
        v ∈ W ∨
          (v.val ∈ Rold.I (cut+1) ∧
            0 < (finiteNumericH L k M).freeLevel v.val) := by
      change v ∈ (W : Set (Fin M)) ∪
        {i : Fin M | i.val ∈ Rold.I (cut+1) ∧
          0 < (finiteNumericH L k M).freeLevel i.val}
        at hStage
      rcases hStage with hW | hSel
      · exact Or.inl (Finset.mem_coe.mp hW)
      · exact Or.inr hSel
    simpa only [hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      using hInput
  have hvFinal :
      v ∈ hStageOriginals L k M W (Rold.I 0) :=
    kpt_physical_stage_originals_subset_final
      family L k M W X oldTop Rold cut hCut hvStage
  apply hNotFinal
  change cut ∈ (hStageOriginals L k M W (Rold.I 0)).image
    (fun q : Fin M => (finiteNumericH L k M).freeLevel q.val)
  exact Finset.mem_image.mpr ⟨v,hvFinal,hEq⟩

/-- The FULL physical K/L base-extension constructs one true old
run Rold, one single finite source-original support W and a finite
exceptional set F of original E-free endpoints with |F|<=M.
At EVERY old-unselected ODD c<oldTop OUTSIDE F, the ONLY remaining
local geometric premise for full candidate Kpt no-novelty is the
complete OLD prefix matching of active physical originals.

The new BARE original's own E-free end is excluded by TRUE
chronological root geometry, not by assuming its name lies in W.
No target run or uniform diary/source orbit is constructed. -/
theorem finiteNumericH_constructed_odd_quiet_outside_finite_freeends
    (family : List (NormalizedForbidden 1 0 1))
    (K L : AgeTestModel 1 0 1)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin 1, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin 0,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin 1,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (hSymL : ∀ i j : Nat,
      (finiteNumericH L k M).L.binary i j (0 : Fin 1) =
        (finiteNumericH L k M).L.binary j i (0 : Fin 1))
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ W : Finset (Fin M),
        ∃ F : Finset Nat,
          Y ⊆ ambientPrefixPool family
            (finiteNumericH L k M) hAvoidL (W : Set (Fin M)) ∧
          F.card ≤ M ∧
          ∀ a : Nat,
            2*a+1 < oldTop →
            2*a+1 ∉ Rold.I (2*a+1) →
            2*a+1 ∉ F →
            KptCandidateOriginalOldPrefixCovered
              family L k M hAvoidL W X Y oldTop Rold (2*a+1) →
            NewRootNoNoveltyAtCut family
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) X)
              (SMTree.Envelope.closure (admissibleKptSTree family)
                (Rold.I ((2*a+1)+1)) Y)
              (2*a+1) := by
  classical
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold,W,hY,hOdd⟩ :=
    finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL hSymL
      U X hSeeds oldTop hOldPhysical
  let F : Finset Nat :=
    KptPhysicalFinalStageFreeEnds family L k M W X oldTop Rold
  have hCard : F.card ≤ M :=
    kpt_physical_final_freeend_cuts_card_le_carrier
      family L k M W X oldTop Rold
  refine ⟨Rold,W,F,hY,hCard,?_⟩
  intro a hCut hOldUnselected hNotF hPrefix
  have hNoEnd :
      ∀ v : Fin M,
        v ∈ ambientStagePool (finiteNumericH L k M)
          (W : Set (Fin M)) (Rold.I ((2*a+1)+1)) →
        (finiteNumericH L k M).freeLevel v.val ≠ 2*a+1 :=
    kpt_physical_no_stage_free_end_outside_final
      family L k M W X oldTop Rold (2*a+1) hCut hNotF
  exact hOdd a hCut hOldUnselected hNoEnd hPrefix

end Kk

#check @Kk.kpt_physical_stage_originals_subset_final
#print axioms Kk.kpt_physical_stage_originals_subset_final
#check @Kk.kpt_physical_final_freeend_cuts_card_le_carrier
#print axioms Kk.kpt_physical_final_freeend_cuts_card_le_carrier
#check @Kk.kpt_physical_no_stage_free_end_outside_final
#print axioms Kk.kpt_physical_no_stage_free_end_outside_final
#check @Kk.finiteNumericH_constructed_odd_quiet_outside_finite_freeends
#print axioms Kk.finiteNumericH_constructed_odd_quiet_outside_finite_freeends
