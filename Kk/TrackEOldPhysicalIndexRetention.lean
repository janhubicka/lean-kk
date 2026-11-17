import Kk.PhysicalOffPlanFiniteIndex
import Mathlib.Tactic

/-!
# Track E E60: old actual Kpt nodes persist physically under genuine height growth

For X ⊆ Y in one normalized Kpt tree and genuine AlgorithmRuns
with oldTop ≤ newTop and one ACTUAL old-top seed, every old pre-cut
complete meet/parameter closure is a literal subset of the new one.
Two independent EXACT finite Kpt node indices then admit a
same-physical-node old-live -> new-live matching at every old cut.

All complete old/upper dependent L+ raw records persist on each
matched actual Kpt node. The old crossing relation is contained
in the new one, NOT conversely; full NEW -> OLD off-plan coverage
remains the substantive unresolved diary geometry.

English-first proof and 18 hostile checks:
docs/track_e_physical_old_node_retention_english_audit.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The actual FULL Kpt pre-cut closure of the old genuine run
is contained in the actual FULL Kpt pre-cut closure of the new
growing-height run. No selected-level or closure equality is assumed. -/
theorem crossheight_actual_preCut_Kpt_source_subset
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (cut : Nat) (hCut : cut < oldTop) :
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunOld.I (cut+1)) X ⊆
    SMTree.Envelope.closure (admissibleKptSTree family)
      (RunNew.I (cut+1)) Y := by
  have hLevels : RunOld.I (cut+1) ⊆ RunNew.I (cut+1) :=
    envelope_algorithmRun_selected_levels_mono_seed_height
      (normalizedKptSMTree family)
      X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew (cut+1) (by omega)
  exact envelope_closure_mono_seeds_and_levels
    (admissibleKptSTree family)
    (RunOld.I (cut+1)) (RunNew.I (cut+1))
    X Y hLevels hXY

/-- Each actual OLD LIVE Kpt node has an IDENTICAL physical node
represented by SOME NEW live index, for each old-range cut.
The two index sets may have DIFFERENT sizes or enumerations.
No bijection of indices and no NEW->OLD coverage is claimed. -/
theorem crossheight_old_live_index_has_same_new_Kpt_node
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
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (cut : Nat) (hCut : cut < oldTop)
    (i : Fin P) (hLive : oldLive cut i = true) :
    ∃ j : Fin Q,
      newLive cut j = true ∧ newNode j = oldNode i := by
  have hOld :
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (cut+1)) X :=
    (hExactOld cut hCut (oldNode i)).mpr ⟨i,rfl,hLive⟩
  have hNew :
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunNew.I (cut+1)) Y :=
    crossheight_actual_preCut_Kpt_source_subset
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew cut hCut hOld
  obtain ⟨j,hName,hNewLive⟩ :=
    (hExactNew cut hCut (oldNode i)).mp hNew
  exact ⟨j,hNewLive,hName⟩

/-- Matching actual old-live source nodes to new-live source nodes
preserves BOTH entire dependent old/upper L+ ancestor records
literally, on the SAME Kpt source node. The raw records contain
auxiliary E and negative L atoms, even across true I2 forks.
This is one-way OLD->NEW; do not infer a common labelled orbit. -/
theorem crossheight_old_live_Kpt_full_Lplus_records_retained
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
    (hExactOld : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (cut+1)) X ↔
        ∃ i : Fin P, oldNode i = z ∧ oldLive cut i = true)
    (hExactNew : ∀ cut : Nat, cut < oldTop →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (cut : Nat) (hCut : cut < oldTop)
    (i : Fin P) (hLive : oldLive cut i = true) :
    ∃ j : Fin Q,
      newLive cut j = true ∧ newNode j = oldNode i ∧
      kptFullOldAtCut (newNode j) cut =
        kptFullOldAtCut (oldNode i) cut ∧
      kptFullUpperAtCut (newNode j) cut =
        kptFullUpperAtCut (oldNode i) cut := by
  obtain ⟨j,hNewLive,hName⟩ :=
    crossheight_old_live_index_has_same_new_Kpt_node
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew oldNode newNode oldLive newLive
      hExactOld hExactNew cut hCut i hLive
  refine ⟨j,hNewLive,hName,?_,?_⟩
  · rw [hName]
  · rw [hName]

/-- Complete old physical full-L+ crossing pairs are necessarily
preserved by the growing-height genuine run, because the entire
old physical pre-cut Kpt closure embeds literally in the new one.
The other inclusion NEW->OLD is the still missing OFF-PLAN
diary source comparison and does not follow from this theorem. -/
theorem crossheight_old_physical_full_crossing_subset_new
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (oldTop newTop : Nat) (hTopLe : oldTop ≤ newTop)
    (hTopSeed : ∃ x ∈ X, LevelTree.lev x = oldTop)
    (RunOld : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (RunNew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (cut : Nat) (hCut : cut < oldTop) :
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunOld.I (cut+1)) X) cut ⊆
    FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (RunNew.I (cut+1)) Y) cut := by
  exact full_physical_crossing_mono_of_source_subset
    family
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RunOld.I (cut+1)) X)
    (SMTree.Envelope.closure (admissibleKptSTree family)
      (RunNew.I (cut+1)) Y)
    (crossheight_actual_preCut_Kpt_source_subset
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew cut hCut) cut

end Kk
