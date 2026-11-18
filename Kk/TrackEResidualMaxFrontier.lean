import Kk.TrackEMaxEligibleCrossingFrontier
import Kk.TrackENumericResidualTwoClass
import Mathlib.Tactic

/-!
# Track E E68: restrict the complete old/upper Kpt frontier to residual names

This is an English-first, *conditional physical source* theorem:
docs/track_e_residual_max_frontier_english_audit_20261118.md

E67 reduces all eligible physical old/upper crossing-cover tests of one
new node to its maximal eligible cut. E68 first removes the old-LIVE
image names, whose physical old witness is the node itself, and then
checks the maximum of the remaining cuts.

E63 supplies the required source-exact old-live data for actual nested
numerical-H+ runs. No terminal/I1, common diary orbit, uniform finite
source carrier, or BRD conclusion is silently asserted here.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For a named actual new source node, retain only its literal
old-boring, off-plan, full-Kpt-new-live crossing cuts at which the
name is NOT in the image of the old-LIVE names. This is NOT the
complement of the full old-FINAL source image. -/
noncomputable def kpt_actual_offplan_residual_node_cuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q) (j : Fin Q) : Finset Nat := by
  classical
  exact
    (kpt_actual_offplan_node_eligible_crossing_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      (newNode j)).filter
      (fun cut => ¬ KptOldLiveImageAt φ oldLive cut j)

/-- Residual eligible membership uses the true complete physical
new pre-cut source, not a selected-original or ordinary-L shadow. -/
theorem mem_kpt_actual_offplan_residual_node_cuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q) (j : Fin Q) (cut : Nat) :
    cut ∈ kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j ↔
    cut ∈ kpt_actual_offplan_node_eligible_crossing_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      (newNode j) ∧
    ¬ KptOldLiveImageAt φ oldLive cut j := by
  classical
  simp only [kpt_actual_offplan_residual_node_cuts,
    Finset.mem_filter]

/-- If an actual new node is the image of a genuinely OLD-LIVE
physical name and it crosses a source cut, then the SAME actual
node is an old physical crossing witness. Its complete old/upper
dependent L+ ancestors match literally, including auxiliary E.
No injectivity of the name map and no I2 functionality is needed. -/
theorem kpt_actual_old_live_image_upper_covered
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hOldSound : ∀ cut : Nat, cut < oldTop →
      ∀ i : Fin P, oldLive cut i = true →
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (cut+1)) X)
    (j : Fin Q) (cut : Nat) (hCut : cut < oldTop)
    (hCross : cut < LevelTree.lev (newNode j))
    (hImage : KptOldLiveImageAt φ oldLive cut j) :
    kpt_actual_run_node_upper_covered
      family X oldTop RunOld (newNode j) cut := by
  obtain ⟨i,hOldLive,hφ⟩ := hImage
  have hNode : newNode j = oldNode i := by
    calc
      newNode j = newNode (φ i) := congrArg newNode hφ.symm
      _ = oldNode i := hNodes i
  refine ⟨newNode j, ?_, hCross, hCross, rfl⟩
  rw [hNode]
  exact hOldSound cut hCut i hOldLive

/-- Full coverage for every eligible crossing of every NEW physical
source name is equivalent to only ONE old complete L+ crossing-cover
test at the MAXIMAL RESIDUAL cut of each name.

The maximal eligible cut without residual filtering is insufficiently
targeted: a matched old-LIVE node at that cut could conceal an EARLIER
newly activated old-FINAL residual source event.

Both AlgorithmRuns are genuine, and the old-live name soundness
premise is physical closure membership, not selected-graph-age
membership. The residual set can be disconnected; downward monotone
OLD source crossing coverage still transfers the SAME old witness. -/
theorem kpt_actual_all_eligible_crossings_iff_residual_max
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hOldSound : ∀ cut : Nat, cut < oldTop →
      ∀ i : Fin P, oldLive cut i = true →
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (cut+1)) X) :
    (∀ j : Fin Q, ∀ cut : Nat,
      cut ∈ kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        (newNode j) →
      kpt_actual_run_node_upper_covered
        family X oldTop RunOld (newNode j) cut) ↔
    (∀ j : Fin Q,
      ∀ (hNonempty :
        (kpt_actual_offplan_residual_node_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          newNode oldLive φ j).Nonempty),
      kpt_actual_run_node_upper_covered
        family X oldTop RunOld (newNode j)
          ((kpt_actual_offplan_residual_node_cuts
            family X Y oldTop newTop RunOld RunNew Allowed
            newNode oldLive φ j).max' hNonempty)) := by
  classical
  constructor
  · intro hAll j hNonempty
    have hMaxMem :
        (kpt_actual_offplan_residual_node_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          newNode oldLive φ j).max' hNonempty ∈
        kpt_actual_offplan_residual_node_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          newNode oldLive φ j :=
      Finset.max'_mem _ hNonempty
    have hBase :=
      ((mem_kpt_actual_offplan_residual_node_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        newNode oldLive φ j _).mp hMaxMem).1
    exact hAll j _ hBase
  · intro hFront j cut hBase
    have hData :=
      (mem_kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        (newNode j) cut).mp hBase
    have hCutOld : cut < oldTop :=
      lt_of_lt_of_le hData.1 (Nat.min_le_left oldTop newTop)
    have hCross : cut < LevelTree.lev (newNode j) :=
      hData.2.2.2.1
    by_cases hImage : KptOldLiveImageAt φ oldLive cut j
    · exact kpt_actual_old_live_image_upper_covered
        family X oldTop RunOld oldNode newNode oldLive φ
        hNodes hOldSound j cut hCutOld hCross hImage
    · let C := kpt_actual_offplan_residual_node_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        newNode oldLive φ j
      have hIn : cut ∈ C :=
        (mem_kpt_actual_offplan_residual_node_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          newNode oldLive φ j cut).mpr ⟨hBase,hImage⟩
      have hNonempty : C.Nonempty := ⟨cut,hIn⟩
      have hMaxMem : C.max' hNonempty ∈ C :=
        Finset.max'_mem C hNonempty
      have hMaxBase :
          C.max' hNonempty ∈
            kpt_actual_offplan_node_eligible_crossing_cuts
              family X Y oldTop newTop RunOld RunNew Allowed
              (newNode j) :=
        ((mem_kpt_actual_offplan_residual_node_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          newNode oldLive φ j _).mp hMaxMem).1
      have hMaxData :=
        (mem_kpt_actual_offplan_node_eligible_crossing_cuts
          family X Y oldTop newTop RunOld RunNew Allowed
          (newNode j) (C.max' hNonempty)).mp hMaxBase
      have hMaxOld : C.max' hNonempty < oldTop :=
        lt_of_lt_of_le hMaxData.1
          (Nat.min_le_left oldTop newTop)
      have hLe : cut ≤ C.max' hNonempty :=
        Finset.le_max' C cut hIn
      have hAtMax : kpt_actual_run_node_upper_covered
          family X oldTop RunOld (newNode j)
          (C.max' hNonempty) := hFront j hNonempty
      exact kpt_actual_run_node_upper_covered_mono_down
        family X oldTop RunOld (newNode j)
        cut (C.max' hNonempty) hLe hMaxOld hAtMax

/-- The exact E65 alternatives for a residual-frontier membership:
a new FINAL name or an old FINAL name inactive in the old pre-cut
closure. Injectivity is needed here for the converse classification,
but NOT for the maximal crossing reduction above. -/
theorem kpt_actual_residual_cut_new_final_or_early_old
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hInjective : Function.Injective φ)
    (j : Fin Q) (cut : Nat)
    (hCut : cut ∈ kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j) :
    KptNewFinalName φ j ∨ KptEarlyOldFinalName φ oldLive cut j := by
  have hResidual :=
    ((mem_kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j cut).mp hCut).2
  exact (kpt_residual_iff_new_final_or_early_old
    φ hInjective oldLive cut j).mp hResidual


/-- Exact exhaustive physical Kpt source indexes with distinct old
names have a DOWNWARD monotone old-live mask. This is a consequence
of genuine AlgorithmRun closure monotonicity, not an assumption about
an arbitrary Boolean index. It discharges H3 of the E68 audit for
the E63 finite numerical-H+ source index. -/
theorem kpt_actual_old_live_down_of_exact_index
    {db du dd P : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (oldTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (oldNode : Fin P → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (hInjective : Function.Injective oldNode)
    (hExact : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (low high : Nat) (i : Fin P)
    (hLe : low ≤ high) (hHigh : high < oldTop)
    (hHighLive : oldLive high i = true) :
    oldLive low i = true := by
  have hHighMember :
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (high+1)) X :=
    (hExact high hHigh (oldNode i)).mpr ⟨i,rfl,hHighLive⟩
  have hLowMember :
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (low+1)) X :=
    (kpt_actual_run_preCut_source_mono_down
      family X oldTop low high RunOld hLe hHigh) hHighMember
  obtain ⟨k,hNode,hLive⟩ :=
    (hExact low (lt_of_le_of_lt hLe hHigh) (oldNode i)).mp hLowMember
  have hki : k = i := hInjective hNode
  rw [hki] at hLive
  exact hLive

/-- Every old-LIVE image at a HIGHER actual source cut remains
old-live at all LOWER cuts, for any fixed map of finite names.
No injectivity of the map is required. -/
theorem kpt_old_live_image_mono_down
    {P Q : Nat}
    (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (oldTop : Nat)
    (hOldDown : ∀ (low high : Nat) (i : Fin P),
      low ≤ high → high < oldTop →
      oldLive high i = true → oldLive low i = true)
    (low high : Nat) (hLe : low ≤ high)
    (hHigh : high < oldTop) (j : Fin Q)
    (hImage : KptOldLiveImageAt φ oldLive high j) :
    KptOldLiveImageAt φ oldLive low j := by
  obtain ⟨i,hLive,hName⟩ := hImage
  exact ⟨i,hOldDown low high i hLe hHigh hLive,hName⟩

/-- Under a monotone OLD-LIVE name mask, being a residual name is
UPWARD CLOSED relative to the actual eligible crossing cut set.
In particular, a HIGHER matched old-live cut cannot hide a LOWER
genuinely residual cut in an exact E63 source index. -/
theorem kpt_actual_residual_eligible_upward_closed
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hOldDown : ∀ (low high : Nat) (i : Fin P),
      low ≤ high → high < oldTop →
      oldLive high i = true → oldLive low i = true)
    (j : Fin Q) (low high : Nat)
    (hLowResidual : low ∈ kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j)
    (hHighEligible : high ∈ kpt_actual_offplan_node_eligible_crossing_cuts
      family X Y oldTop newTop RunOld RunNew Allowed (newNode j))
    (hLe : low ≤ high) :
    high ∈ kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j := by
  have hLowNotImage :=
    ((mem_kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j low).mp hLowResidual).2
  have hHighData :=
    (mem_kpt_actual_offplan_node_eligible_crossing_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      (newNode j) high).mp hHighEligible
  have hHighOld : high < oldTop :=
    lt_of_lt_of_le hHighData.1
      (Nat.min_le_left oldTop newTop)
  have hHighNotImage : ¬ KptOldLiveImageAt φ oldLive high j := by
    intro hHighImage
    exact hLowNotImage
      (kpt_old_live_image_mono_down
        φ oldLive oldTop hOldDown
        low high hLe hHighOld j hHighImage)
  exact (mem_kpt_actual_offplan_residual_node_cuts
    family X Y oldTop newTop RunOld RunNew Allowed
    newNode oldLive φ j high).mpr ⟨hHighEligible,hHighNotImage⟩

/-- With genuinely monotone old-live masks, a nonempty residual
frontier has EXACTLY THE SAME MAXIMUM as the unrestricted E67
eligible frontier. There are not two different physical frontier
cuts to control. E68.2 is a useful residual factorization but not
a stronger geometric old-crossing theorem than E67 itself. -/
theorem kpt_actual_residual_max_eq_eligible_max
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (φ : Fin P → Fin Q)
    (hOldDown : ∀ (low high : Nat) (i : Fin P),
      low ≤ high → high < oldTop →
      oldLive high i = true → oldLive low i = true)
    (j : Fin Q)
    (hResidualNonempty :
      (kpt_actual_offplan_residual_node_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        newNode oldLive φ j).Nonempty) :
    ∃ (hEligibleNonempty :
      (kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        (newNode j)).Nonempty),
      (kpt_actual_offplan_residual_node_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        newNode oldLive φ j).max' hResidualNonempty =
      (kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop RunOld RunNew Allowed
        (newNode j)).max' hEligibleNonempty := by
  let R := kpt_actual_offplan_residual_node_cuts
    family X Y oldTop newTop RunOld RunNew Allowed
    newNode oldLive φ j
  let E := kpt_actual_offplan_node_eligible_crossing_cuts
    family X Y oldTop newTop RunOld RunNew Allowed (newNode j)
  have hRmaxMem : R.max' hResidualNonempty ∈ R :=
    Finset.max'_mem R hResidualNonempty
  have hRmaxEligible : R.max' hResidualNonempty ∈ E :=
    ((mem_kpt_actual_offplan_residual_node_cuts
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ j _).mp hRmaxMem).1
  have hEligibleNonempty : E.Nonempty :=
    ⟨R.max' hResidualNonempty,hRmaxEligible⟩
  refine ⟨hEligibleNonempty,?_⟩
  have hEmaxMem : E.max' hEligibleNonempty ∈ E :=
    Finset.max'_mem E hEligibleNonempty
  have hLe : R.max' hResidualNonempty ≤ E.max' hEligibleNonempty :=
    Finset.le_max' E _ hRmaxEligible
  have hEmaxResidual : E.max' hEligibleNonempty ∈ R :=
    kpt_actual_residual_eligible_upward_closed
      family X Y oldTop newTop RunOld RunNew Allowed
      newNode oldLive φ hOldDown j
      (R.max' hResidualNonempty) (E.max' hEligibleNonempty)
      hRmaxMem hEmaxMem hLe
  have hLeReverse :
      E.max' hEligibleNonempty ≤ R.max' hResidualNonempty :=
    Finset.le_max' R _ hEmaxResidual
  exact le_antisymm hLe hLeReverse

end Kk
