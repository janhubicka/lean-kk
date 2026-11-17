import Kk.TrackENumericCoherentSourceIndex
import Kk.PhysicalBareNewRootRun
import Kk.PhysicalCrossHeightConstructedWitness
import Mathlib.Tactic

/-!
# Track C: genuine physical OLD→NEW coherent Kpt source index

English proof and adversarial audit were committed before this Lean code:
  docs/track_c_constructed_physical_old_new_index_english_audit.md

Start with a genuine OLD physical exhaustive Kpt AlgorithmRun, complete
old/new numerical-H+ original columns, true forbidden avoidance and ONE
actual new Kpt original at its physically computed free-level top.

CONSTRUCT the genuine NEW bare-root AlgorithmRun (not an input run),
derive oldTop≤newTop from the physically represented old top source,
and produce BOTH exhaustive finite Kpt indexes plus ONE injection
oldIndex→newIndex preserving the literal old Kpt nodes, ALL old cut
live bits, and full old/upper dependent L+/E ancestor records.

This is strictly OLD→NEW and uses the SAME normalized Kpt successor
tree; it is NOT a reverse no-novelty, diary-uniform source, common
fully labelled inverse monoid orbit, or any BRD theorem.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- From a REAL finite H+ physical extension, construct a genuine old
and new AlgorithmRun and one coherent OLD→NEW injection of the full
Kpt source-node indexes.

The physical hypotheses require old/new complete original-column
agreement, both whole-structure forbidden-family avoidance, exact
old original-prefix seed representation, a genuine old top seed and
an actual new top original. Neither next-run existence nor source
index-exhaustiveness nor the height inequality is postulated.

Old source names are injected into new names by literal SAME Kpt
node identity, preserving all old-live cuts and complete raw L+/E
old/upper types. No assertion that every NEW node has an OLD mate
or that arbitrary diary occurrences share an inverse orbit. -/
theorem finiteNumericH_constructed_old_new_coherent_source_index
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
    (hOldPhysical : HasPhysicalExhaustiveKptRun family X oldTop) :
    let top : Nat := hPosition k (j-1) k+1
    let Y : Set (AdmissibleKptNode family) :=
      finiteNumericH_bareTopRootSeeds
        family L k M j hAvoidL hTarget X
    ∃ Rold : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) X oldTop,
      ∃ Rnew : SMTree.Envelope.AlgorithmRun
          (normalizedKptSMTree family) Y top,
        ∃ oldParams newParams : Finset (AdmissibleKptNode family),
          ∃ oldLive : Nat → Fin oldParams.card → Bool,
            ∃ newLive : Nat → Fin newParams.card → Bool,
              ∃ φ : Fin oldParams.card → Fin newParams.card,
                Function.Injective φ ∧
                (∀ i : Fin oldParams.card,
                  (newParams.equivFin.symm (φ i)).val =
                    (oldParams.equivFin.symm i).val) ∧
                (∀ cut : Nat, cut < oldTop →
                  ∀ z : AdmissibleKptNode family,
                    z ∈ SMTree.Envelope.closure
                      (admissibleKptSTree family)
                      (Rold.I (cut+1)) X ↔
                    ∃ i : Fin oldParams.card,
                      (oldParams.equivFin.symm i).val = z ∧
                      oldLive cut i = true) ∧
                (∀ cut : Nat, cut < oldTop →
                  ∀ z : AdmissibleKptNode family,
                    z ∈ SMTree.Envelope.closure
                      (admissibleKptSTree family)
                      (Rnew.I (cut+1)) Y ↔
                    ∃ i : Fin newParams.card,
                      (newParams.equivFin.symm i).val = z ∧
                      newLive cut i = true) ∧
                (∀ cut : Nat, cut < oldTop →
                  ∀ i : Fin oldParams.card,
                    oldLive cut i = true →
                      newLive cut (φ i) = true) ∧
                (∀ cut : Nat, cut < oldTop →
                  ∀ i : Fin oldParams.card,
                    kptFullOldAtCut
                      ((newParams.equivFin.symm (φ i)).val) cut =
                        kptFullOldAtCut
                          ((oldParams.equivFin.symm i).val) cut ∧
                    kptFullUpperAtCut
                      ((newParams.equivFin.symm (φ i)).val) cut =
                        kptFullUpperAtCut
                          ((oldParams.equivFin.symm i).val) cut) ∧
                (∀ ψ : Fin oldParams.card → Fin newParams.card,
                  (∀ i : Fin oldParams.card,
                    (newParams.equivFin.symm (ψ i)).val =
                      (oldParams.equivFin.symm i).val) →
                  ψ = φ) := by
  classical
  let top : Nat := hPosition k (j-1) k+1
  let Y : Set (AdmissibleKptNode family) :=
    finiteNumericH_bareTopRootSeeds
      family L k M j hAvoidL hTarget X
  obtain ⟨Rold, hOldTopSeed, _oldParams, _oldLive,
    _oldExact, _oldInj, _oldMask, _oldCover⟩ := hOldPhysical
  have hOldLe : oldTop ≤ top :=
    finiteNumericH_old_physical_top_le_new_chronological_top
      family K k N j oldTop hNTop hAvoidK U X hSeeds hOldTopSeed
  have hNewPhysical : HasPhysicalExhaustiveKptRun family Y top :=
    (finiteNumericH_bareTopRoot_construct_exhaustive_run
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)).2
  obtain ⟨Rnew, _hNewTopSeed, _newParams, _newLive,
    _newExact, _newInj, _newMask, _newCover⟩ := hNewPhysical
  obtain ⟨V, hNewCover, _hBound, _hTop⟩ :=
    finiteNumericH_bareTopRoot_seeds_represented_bounded
      family K L k b N M j hNM hBlock hk hj hTarget hNTop
      hBin hUn hDiag hAvoidK hAvoidL U X hSeeds (Rold.I 0)
  have hXY : X ⊆ Y := by
    intro z hz
    exact Or.inl hz
  have hOldCoverNew :
      X ⊆ ambientPrefixPool family
        (finiteNumericH L k M) hAvoidL V :=
    hXY.trans hNewCover
  obtain ⟨oldParams, newParams, oldLive, newLive,
    φ, hInjective, hSameNodes, hOldExact, hNewExact,
    hOldLiveTransfer, hFullTypes, hUnique⟩ :=
    finiteNumericH_actual_nested_runs_coherent_source_index
      family L k M hAvoidL V X Y hOldCoverNew hNewCover hXY
      oldTop top hOldLe hOldTopSeed Rold Rnew
  exact ⟨Rold, Rnew, oldParams, newParams, oldLive, newLive,
    φ, hInjective, hSameNodes, hOldExact, hNewExact,
    hOldLiveTransfer, hFullTypes, hUnique⟩

end Kk
