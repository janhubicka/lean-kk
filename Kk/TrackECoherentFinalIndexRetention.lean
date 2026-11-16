import Kk.TrackEOldPhysicalIndexRetention
import Mathlib.Tactic

/-!
# Track E E62: one coherent final-index embedding across ALL old Kpt cuts

E60 proves physical old->new retention cut by cut. If the two finite
indices exhaust genuine FINAL Kpt closures, the same old physical Kpt
node is in the new FINAL closure, so one can choose a SINGLE new index
for each old index before inspecting any cut. This yields an injective
name embedding preserving every old-live event and every raw L+ ancestor
record, uniformly over old scan cuts. It is unique if the NEW final
enumeration is injective. The reverse NEW->OLD off-plan matching and
the cross-occurrence labelled diary orbit are still OPEN.

English-first proof and 20 hostile cases:
docs/track_e_coherent_physical_old_index_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The two genuine final physical Kpt closure indices have a single
old->new injection of names preserving the SAME physical node,
all old-range cut membership, and both complete old/upper dependent
L+ ancestor records. No equality of finite index sizes is needed.

This theorem is NOT a correspondence between two unrelated diary
occurrences or a NEW->OLD no-novelty criterion. -/
theorem crossheight_coherent_old_final_index_embedding
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (hOldInjective : Function.Injective oldNode)
    (hOldFinal : ∀ i : Fin P,
      oldNode i ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I 0) X)
    (hNewFinalExact : ∀ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I 0) Y ↔
      ∃ j : Fin Q, newNode j = z)
    (hOldLive : ∀ cut : Nat, cut < oldTop →
      ∀ i : Fin P, oldLive cut i = true →
        oldNode i ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunOld.I (cut+1)) X)
    (hNewLive : ∀ cut : Nat, cut < oldTop →
      ∀ j : Fin Q,
        newLive cut j = true ↔
        newNode j ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (RunNew.I (cut+1)) Y) :
    ∃ φ : Fin P → Fin Q,
      Function.Injective φ ∧
      (∀ i : Fin P, newNode (φ i) = oldNode i) ∧
      (∀ cut : Nat, cut < oldTop →
        ∀ i : Fin P, oldLive cut i = true →
          newLive cut (φ i) = true) ∧
      (∀ cut : Nat, cut < oldTop →
        ∀ i : Fin P,
          kptFullOldAtCut (newNode (φ i)) cut =
            kptFullOldAtCut (oldNode i) cut ∧
          kptFullUpperAtCut (newNode (φ i)) cut =
            kptFullUpperAtCut (oldNode i) cut) := by
  classical
  have hLevels : RunOld.I 0 ⊆ RunNew.I 0 :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      (normalizedKptSMTree family)
      X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew 0 (by omega)
  have hFinal :
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I 0) X ⊆
      SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I 0) Y :=
    envelope_closure_mono_seeds_and_levels
      (admissibleKptSTree family)
      (RunOld.I 0) (RunNew.I 0) X Y hLevels hXY
  have hChoice : ∀ i : Fin P, ∃ j : Fin Q,
      newNode j = oldNode i := by
    intro i
    exact (hNewFinalExact (oldNode i)).mp (hFinal (hOldFinal i))
  let φ : Fin P → Fin Q := fun i => Classical.choose (hChoice i)
  have hName : ∀ i : Fin P, newNode (φ i) = oldNode i := by
    intro i
    exact Classical.choose_spec (hChoice i)
  have hInjective : Function.Injective φ := by
    intro i j hij
    apply hOldInjective
    calc
      oldNode i = newNode (φ i) := (hName i).symm
      _ = newNode (φ j) := congrArg newNode hij
      _ = oldNode j := hName j
  refine ⟨φ, hInjective, hName, ?_, ?_⟩
  · intro cut hCut i hLiveOld
    have hInOld :
        oldNode i ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (RunOld.I (cut+1)) X :=
      hOldLive cut hCut i hLiveOld
    have hInNew :
        oldNode i ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (RunNew.I (cut+1)) Y :=
      crossheight_actual_preCut_Kpt_source_subset
        family X Y hXY oldTop newTop hTopLe hTopSeed
        RunOld RunNew cut hCut hInOld
    apply (hNewLive cut hCut (φ i)).2
    rw [hName i]
    exact hInNew
  · intro cut hCut i
    constructor
    · rw [hName i]
    · rw [hName i]

/-- If the new final physical Kpt index itself is injective,
its numerical name for any fixed old Kpt node is unique.
Thus any two coherent old->new index transports preserving
actual Kpt node identity are the SAME name map. -/
theorem crossheight_coherent_final_index_embedding_unique
    {db du dd P Q : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (hNewInjective : Function.Injective newNode)
    (φ ψ : Fin P → Fin Q)
    (hφ : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hψ : ∀ i : Fin P, newNode (ψ i) = oldNode i) :
    φ = ψ := by
  funext i
  apply hNewInjective
  exact (hφ i).trans (hψ i).symm

end Kk
