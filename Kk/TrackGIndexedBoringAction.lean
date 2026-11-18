import Kk.TrackGCrossheightBoringAction
import Kk.TrackEOldPhysicalIndexRetention
import Mathlib.Tactic

/-!
# Track G: finite indexed old-to-new FULL Kpt source and boring-factor action.

English proof and 18 hostile checks committed FIRST:
docs/track_g_indexed_boring_action_english_audit_20261118.md

Combines merged G336's ACTUAL old-source ancestor-action naturality
with the existing E60 exact finite physical source-index retention.
ONE pair of genuine accumulated MMaps works simultaneously for ALL
old live Kpt names of level above cut; each has a new live name for
the same physical node and hence identical FULL dependent old/upper
L+/E records. No reverse/new-only map or global BRD is asserted.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.SMTree
open SuccessorTree.V10

/-- For nested genuine Kpt runs and exact finite pre-cut source
indices, every high-level OLD live source name has a NEW live name
for the IDENTICAL actual Kpt node, with all full dependent old/upper
L+/E types retained, and one common pair of total boring-block
factors acting identically on its lower source ancestor.

The all-boring hypothesis is on BOTH actual complete Kpt closures,
not on selected front age shadows. No inverse source bijection. -/
theorem crossheight_indexed_boring_action_preserves_old_Lplus_records
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
    (low cut : Nat) (hLowCut : low ≤ cut+1)
    (hCut : cut < oldTop)
    (hBoringOld : ∀ i : Nat, low ≤ i → i < cut+1 →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunOld.I (i+1)) X) i)
    (hBoringNew : ∀ i : Nat, low ≤ i → i < cut+1 →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RunNew.I (i+1)) Y) i) :
    ∃ Dold Dnew : MMap (normalizedKptSMTree family),
      RunOld.F low = MMap.comp (normalizedKptSMTree family)
        (RunOld.F (cut+1)) Dold ∧
      RunNew.F low = MMap.comp (normalizedKptSMTree family)
        (RunNew.F (cut+1)) Dnew ∧
      ∀ (i : Fin P) (hLive : oldLive cut i = true)
        (hLev : cut+1 ≤ LevelTree.lev (oldNode i)),
        ∃ j : Fin Q,
          newLive cut j = true ∧
          newNode j = oldNode i ∧
          kptFullOldAtCut (newNode j) cut =
            kptFullOldAtCut (oldNode i) cut ∧
          kptFullUpperAtCut (newNode j) cut =
            kptFullUpperAtCut (oldNode i) cut ∧
          Dold (LevelTree.ancestor (oldNode i) low
            (le_trans hLowCut hLev)) =
          Dnew (LevelTree.ancestor (oldNode i) low
            (le_trans hLowCut hLev)) := by
  obtain ⟨Dold, Dnew, hDold, hDnew, hAction⟩ :=
    crossheight_actual_boring_factor_agrees_on_old_Kpt_source
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew low cut hLowCut hCut hBoringOld hBoringNew
  refine ⟨Dold, Dnew, hDold, hDnew, ?_⟩
  intro i hLive hLev
  have hcOld :
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (RunOld.I (cut+1)) X :=
    (hExactOld cut hCut (oldNode i)).mpr ⟨i,rfl,hLive⟩
  obtain ⟨j, hNewLive, hNode, hOld, hUpper⟩ :=
    crossheight_old_live_Kpt_full_Lplus_records_retained
      family X Y hXY oldTop newTop hTopLe hTopSeed
      RunOld RunNew oldNode newNode oldLive newLive
      hExactOld hExactNew cut hCut i hLive
  exact ⟨j, hNewLive, hNode, hOld, hUpper,
    hAction (oldNode i) hcOld hLev⟩

end Kk
