import Kk.TrackEPhysicalFailureFlags
import Mathlib.Tactic

/-!
# Track G: intrinsic physical bad cuts have genuine NEW-ONLY Kpt node witnesses

Track E E55's independently verified physical failure flags say that a
bad cut has a new terminal (without an old terminal) OR a missing full
old/upper dependent L+ crossing pair. Here we lift these flags to
ONE ACTUAL Kpt node in the NEW physical source but not the OLD source.

Unlike Track E's new-SELECTED-cut witness theorem, this works at
EVERY physical bad cut, even when the enlarged AlgorithmRun does not
select it. The pair keeps full E/negative-L bits and all I2 forks.

English-first proof, non-implication counterexample and hostile audit:
docs/track_g_badcut_novel_node_witness_english_audit_20261117.md

This does not bound the NUMBER of bad cuts by the number of new nodes:
one high-level node can cross many cuts. No diary-uniform Extra budget,
common labelled source orbit or exact BRD theorem is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- One actual NEW source node, absent from OLD, causes the terminal
failure or witnesses a COMPLETE old/upper L+ pair absent from OLD.
The pair's two ancestors belong to this SAME actual node. -/
def KptPhysicalNovelNodeAtCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Zold Znew : Set (AdmissibleKptNode family))
    (cut : Nat) : Prop :=
  ∃ z : AdmissibleKptNode family,
    z ∈ Znew ∧ z ∉ Zold ∧
    (LevelTree.lev z = cut ∨
      ∃ p : PartialTypeWithE cut db du dd ×
          PartialTypeWithE (cut+1) db du dd,
        p ∉ FullPhysicalClosureCrossing family Zold cut ∧
        ∃ (hz : cut < LevelTree.lev z),
          (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
            (LevelTree.ancestor z cut (Nat.le_of_lt hz)).val ∧
          (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
            (LevelTree.ancestor z (cut+1)
              (Nat.succ_le_iff.mpr hz)).val)

/-- Any genuine terminal-or-crossing failure has a NEW-ONLY physical
Kpt source node witness. No old/new source inclusion, AlgorithmRun,
finite index or chosen graph-age shadow is assumed. -/
theorem kptPhysicalCutFailure_has_novel_node_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Zold Znew : Set (AdmissibleKptNode family))
    (cut : Nat)
    (hFail : KptPhysicalCutFailure family Zold Znew cut) :
    KptPhysicalNovelNodeAtCut family Zold Znew cut := by
  classical
  change KptPhysicalTerminalFailure family Zold Znew cut ∨
    KptPhysicalCrossingFailure family Zold Znew cut at hFail
  rcases hFail with hTerminal | hCross
  · obtain ⟨⟨z,hNew,hLev⟩,hNoOld⟩ := hTerminal
    refine ⟨z,hNew,?_,Or.inl hLev⟩
    intro hOldZ
    exact hNoOld ⟨z,hOldZ,hLev⟩
  · have hMissing :
        ∃ p : PartialTypeWithE cut db du dd ×
            PartialTypeWithE (cut+1) db du dd,
          p ∈ FullPhysicalClosureCrossing family Znew cut ∧
          p ∉ FullPhysicalClosureCrossing family Zold cut := by
      by_contra hNone
      apply hCross
      intro p hNewPair
      by_contra hOldMissing
      exact hNone ⟨p,hNewPair,hOldMissing⟩
    obtain ⟨p,hNewPair,hNotOldPair⟩ := hMissing
    obtain ⟨z,hNew,hCut,hOldAnc,hUpperAnc⟩ := hNewPair
    refine ⟨z,hNew,?_,Or.inr ?_⟩
    · intro hOldZ
      exact hNotOldPair ⟨z,hOldZ,hCut,hOldAnc,hUpperAnc⟩
    · exact ⟨p,hNotOldPair,hCut,hOldAnc,hUpperAnc⟩

/-- EVERY member of E55's intrinsic bad-cut Finset has an actual
new-only physical Kpt source node, even when it is not a newly
selected cut in either AlgorithmRun.

Neither the number of source nodes nor their numerical heights
bounds this bad-cut support uniformly in a diary. -/
theorem kptPhysicalBadCut_has_novel_node_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (oldSelected : Nat → Set Nat)
    (oldTop : Nat)
    (oldSource newSource : Nat → Set (AdmissibleKptNode family))
    (cut : Nat)
    (hBad : cut ∈ kptPhysicalBadCuts family oldSelected oldTop
      oldSource newSource) :
    cut < oldTop ∧ cut ∉ oldSelected cut ∧
      KptPhysicalNovelNodeAtCut family
        (oldSource cut) (newSource cut) cut := by
  obtain ⟨hCut,hBoring,hFail⟩ :=
    (mem_kptPhysicalBadCuts family oldSelected oldTop
      oldSource newSource cut).mp hBad
  exact ⟨hCut,hBoring,
    kptPhysicalCutFailure_has_novel_node_witness
      family (oldSource cut) (newSource cut) cut hFail⟩

end Kk
