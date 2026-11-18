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

end Kk
