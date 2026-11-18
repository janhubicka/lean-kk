import Kk.PhysicalLiveSourceResidual
import Kk.TrackEResidualLiveNovelty

/-!
Track C: genuine physical numerical-H+ off-plan no-novelty is equivalent
to residual-source quietness at old-boring cuts.

English first: docs/track_c_constructed_physical_offplan_residual_audit.md
The physical constructor supplies the AlgorithmRuns and exact source
indexes; the checked E64 theorem reduces the full no-novelty test to
the residual new-live names outside the old-LIVE image. Neither
quietness itself nor a diary-uniform event schedule is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

theorem finiteNumericH_constructed_offplan_iff_residual_quiet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K L : AgeTestModel db du dd)
    (k b N M j : Nat)
    (hNM : N ≤ M) (hBlock : N ≤ hPosition k b 0)
    (hk : 0 < k) (hj : 0 < j)
    (hTarget : hPosition k j k < M)
    (hNTop : N ≤ hPosition k (j-1) k+1)
    (hBin : ∀ i j : Nat, i < b → j < b →
      ∀ r : Fin db, K.binary i j r = L.binary i j r)
    (hUn : ∀ i : Nat, i < b → ∀ r : Fin du,
      K.unary i r = L.unary i r)
    (hDiag : ∀ i : Nat, i < b → ∀ r : Fin dd,
      K.diagonal i r = L.diagonal i r)
    (hAvoidK : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (hAvoidL : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH L k M).L)
    (U : Set (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hSeeds : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoidK U)
    (oldTop : Nat)
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop)
    (Allowed : Set Nat) :
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ oldParams newParams : Finset (AdmissibleKptNode family),
        ∃ oldLive : Nat → Fin oldParams.card → Bool,
          ∃ newLive : Nat → Fin newParams.card → Bool,
            ∃ e : CoherentKptIndex family
              (fun i : Fin oldParams.card =>
                (oldParams.equivFin.symm i).val)
              (fun q : Fin newParams.card =>
                (newParams.equivFin.symm q).val)
              oldLive newLive oldTop,
              (KptTwoIndexOffPlanNoNovelty family Rold.I
                oldTop Allowed
                (fun i : Fin oldParams.card =>
                  (oldParams.equivFin.symm i).val)
                (fun q : Fin newParams.card =>
                  (newParams.equivFin.symm q).val)
                oldLive newLive ↔
               ∀ cut : Nat, cut < oldTop →
                 cut ∉ Rold.I cut → cut ∉ Allowed →
                 KptResidualQuietAtBoringCut family
                   (fun i : Fin oldParams.card =>
                     (oldParams.equivFin.symm i).val)
                   (fun q : Fin newParams.card =>
                     (newParams.equivFin.symm q).val)
                   oldLive newLive e.map cut) := by
  classical
  obtain ⟨Rold, _Rnew, oldParams, newParams,
    oldLive, newLive, e, hOldExact, _hNewExact,
    _hFullTypes, _hUnique⟩ :=
    finiteNumericH_constructed_composable_coherent_source_index
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds oldTop hOldPhysical
  refine ⟨Rold, oldParams, newParams, oldLive, newLive, e, ?_⟩
  exact actual_Kpt_twoIndex_offplan_iff_residual_live_quiet
    family X oldTop Rold Allowed
    (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
    (fun q : Fin newParams.card => (newParams.equivFin.symm q).val)
    oldLive newLive e.map e.same_node hOldExact

end Kk

#check @Kk.finiteNumericH_constructed_offplan_iff_residual_quiet
#print axioms Kk.finiteNumericH_constructed_offplan_iff_residual_quiet
