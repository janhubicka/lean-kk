import Kk.TrackEResidualLiveNovelty
import Mathlib.Tactic

/-!
# Track E E65: exact two classes of residual new Kpt names

For an INJECTIVE coherent old-final->new-final physical Kpt
index map, residual at cut c means outside the image of the
OLD-LIVE indices at that cut. It is EQUIVALENT to:
  1. a genuinely new final source index, or
  2. an OLD final source index which is not active yet at c
     in the OLD run, but may be active earlier in the NEW run.

This dichotomy is essential: restricting to completely new
final source nodes would miss newly activated OLD-final nodes.

The E63 real numerical-H+ coherent finite indices and E64's
residual reduction compose to give an exact residual-only
off-plan testing criterion for TWO genuine nested physical
numerical-H+ runs in ONE normalized Kpt source.

English-first proof and 18 hostile cases:
  docs/track_e_numeric_residual_two_class_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A genuinely NEW FINAL physical name, outside the full
image of the coherent old-final Kpt source enumeration. -/
def KptNewFinalName
    {P Q : Nat} (φ : Fin P → Fin Q) (j : Fin Q) : Prop :=
  ¬ ∃ i : Fin P, φ i = j

/-- An OLD FINAL physical Kpt name, but not active in the
OLD pre-cut closure at cut c. If newLive c j=true it is
a genuinely newly activated old-final parameter event. -/
def KptEarlyOldFinalName
    {P Q : Nat} (φ : Fin P → Fin Q)
    (oldLive : Nat → Fin P → Bool)
    (cut : Nat) (j : Fin Q) : Prop :=
  ∃ i : Fin P, φ i = j ∧ oldLive cut i = false

/-- For an INJECTIVE coherent physical source-name map, a
new index is outside the old-LIVE image at cut c IFF it
is outside the entire old FINAL image OR is an old-final
name inactive in the old pre-cut closure.

The converse fails for noninjective φ, so this hypothesis
must not be dropped or replaced by graph-age matching. -/
theorem kpt_residual_iff_new_final_or_early_old
    {P Q : Nat}
    (φ : Fin P → Fin Q)
    (hInjective : Function.Injective φ)
    (oldLive : Nat → Fin P → Bool)
    (cut : Nat) (j : Fin Q) :
    (¬ KptOldLiveImageAt φ oldLive cut j) ↔
      KptNewFinalName φ j ∨
      KptEarlyOldFinalName φ oldLive cut j := by
  classical
  constructor
  · intro hResidual
    by_cases hImage : ∃ i : Fin P, φ i = j
    · obtain ⟨i,hi⟩ := hImage
      right
      refine ⟨i,hi,?_⟩
      cases hOld : oldLive cut i with
      | false => rfl
      | true =>
        exact False.elim (hResidual ⟨i,hOld,hi⟩)
    · exact Or.inl hImage
  · rintro (hNoImage | ⟨i,hi,hFalse⟩) ⟨k,hOldLive,hk⟩
    · exact hNoImage ⟨k,hk⟩
    · have hik : i = k := hInjective (hi.trans hk.symm)
      subst k
      rw [hFalse] at hOldLive
      cases hOldLive

/-- The correct finite geometric certificate is now completely
explicit: TWO true nested physical numerical-H+ Kpt AlgorithmRuns
supply BOTH exact full source indices, ONE coherent injective name
map, all old-live retention and an EXACT equivalence between the
full two-index off-plan no-novelty test and tests restricted to
residual NEW-LIVE source names at OLD-BORING off-plan cuts.

This is NOT a proof the residual conditions hold. It is not a
construction of a uniform diary microevent set, source-coordinate
normalization between unrelated occurrences or a common labelled
inverse-source orbit. -/
theorem finiteNumericH_nested_runs_offplan_iff_residual_live
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Set (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid U)
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat) :
    ∃ oldParams newParams : Finset (AdmissibleKptNode family),
      ∃ oldLive : Nat → Fin oldParams.card → Bool,
      ∃ newLive : Nat → Fin newParams.card → Bool,
      ∃ φ : Fin oldParams.card → Fin newParams.card,
        Function.Injective φ ∧
        (∀ i : Fin oldParams.card,
          (newParams.equivFin.symm (φ i)).val =
            (oldParams.equivFin.symm i).val) ∧
        (∀ cut : Nat, cut < oldTop →
          ∀ i : Fin oldParams.card,
            oldLive cut i = true →
              newLive cut (φ i) = true) ∧
        (KptTwoIndexOffPlanNoNovelty family RunOld.I
          oldTop Allowed
          (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
          (fun j : Fin newParams.card => (newParams.equivFin.symm j).val)
          oldLive newLive ↔
         ∀ cut : Nat, cut < oldTop →
           cut ∉ RunOld.I cut → cut ∉ Allowed →
           KptResidualQuietAtBoringCut family
             (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
             (fun j : Fin newParams.card => (newParams.equivFin.symm j).val)
             oldLive newLive φ cut) := by
  classical
  obtain ⟨oldParams,newParams,oldLive,newLive,φ,
    hInjective,hNames,hOldExact,_hNewExact,hLive,
    _hFullTypes,_hUnique⟩ :=
    finiteNumericH_actual_nested_runs_coherent_source_index
      family K k N hAvoid U X Y
      hX hY hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew
  refine ⟨oldParams,newParams,oldLive,newLive,φ,
    hInjective,hNames,hLive,?_⟩
  exact actual_Kpt_twoIndex_offplan_iff_residual_live_quiet
    family X oldTop RunOld Allowed
    (fun i : Fin oldParams.card => (oldParams.equivFin.symm i).val)
    (fun j : Fin newParams.card => (newParams.equivFin.symm j).val)
    oldLive newLive φ hNames hOldExact

end Kk
