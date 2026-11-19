import Kk.ConstructedPhysicalOffPlanResidual
import Kk.ResidualTwoClassQuiet

/-!
Track C: physical H+ source comparison equivalently reduces to TWO
separate full dependent L+/E residual quietness obligations:
early-old activation and literally new-final source indices.
No quietness is proved; the constructed physical hypotheses remain
identical to the original source-index theorem.

English first: docs/track_c_physical_two_class_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

theorem finiteNumericH_constructed_offplan_iff_two_residual_classes
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
                 (KptResidualClassQuiet family
                    (fun i : Fin oldParams.card =>
                      (oldParams.equivFin.symm i).val)
                    (fun q : Fin newParams.card =>
                      (newParams.equivFin.symm q).val)
                    oldLive newLive cut (KptNewFinalName e.map) ∧
                  KptResidualClassQuiet family
                    (fun i : Fin oldParams.card =>
                      (oldParams.equivFin.symm i).val)
                    (fun q : Fin newParams.card =>
                      (newParams.equivFin.symm q).val)
                    oldLive newLive cut
                    (KptEarlyOldFinalName e.map oldLive cut))) := by
  classical
  obtain ⟨Rold, _Rnew, oldParams, newParams,
    oldLive, newLive, e, hOldExact, _hNewExact,
    _hFullTypes, _hUnique⟩ :=
    finiteNumericH_constructed_composable_coherent_source_index
      family K L k b N M j
      hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds oldTop hOldPhysical
  refine ⟨Rold, oldParams, newParams, oldLive, newLive, e, ?_⟩
  have hBase :=
    actual_Kpt_twoIndex_offplan_iff_residual_live_quiet
      family X oldTop Rold Allowed
      (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
      (fun q : Fin newParams.card => (newParams.equivFin.symm q).val)
      oldLive newLive e.map e.same_node hOldExact
  constructor
  · intro hNoNovelty cut hCut hBoring hOffPlan
    exact (kpt_residual_quiet_iff_two_classes family
      (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
      (fun q : Fin newParams.card => (newParams.equivFin.symm q).val)
      oldLive newLive e.map e.map_injective cut).mp
      (hBase.mp hNoNovelty cut hCut hBoring hOffPlan)
  · intro hTwoClass
    apply hBase.mpr
    intro cut hCut hBoring hOffPlan
    exact (kpt_residual_quiet_iff_two_classes family
      (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
      (fun q : Fin newParams.card => (newParams.equivFin.symm q).val)
      oldLive newLive e.map e.map_injective cut).mpr
      (hTwoClass cut hCut hBoring hOffPlan)


end Kk

#check @Kk.finiteNumericH_constructed_offplan_iff_two_residual_classes
#print axioms Kk.finiteNumericH_constructed_offplan_iff_two_residual_classes
