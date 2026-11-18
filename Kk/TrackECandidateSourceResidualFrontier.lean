import Kk.TrackEResidualMaxFrontier
import Kk.TrackGBoringOnlyNoNoveltyRunTransfer
import Mathlib.Tactic

/-!
# Track E E69: maximal physical candidate-source certificate constructs a new run

English proof and 21 hostile checks were committed FIRST:
  docs/track_e_candidate_source_residual_max_english_audit_20261118.md

Only an OLD genuine AlgorithmRun R on X is assumed. At each old cut
the proposed enlarged physical Kpt source is closure_(R.I(c+1))(Y),
not the closure of an independently assumed AlgorithmRun on Y.

Exact indexing of these candidate sources, absent new terminals at
old-boring cuts and one physical upper-crossing cover at the maximal
residual candidate cut per new name imply physical no-novelty at ALL
old-boring cuts. Thus verified Track G creates a REAL synchronized
AlgorithmRun on Y with identical I and TOTAL F. The candidate source
index and geometric maximal tests are explicit application premises.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- For a named candidate new Kpt source node, cuts of the OLD
genuine run that are genuinely boring, at which the node crosses and
is NEW-LIVE in the candidate closure, and is not an OLD-LIVE image.

No Y AlgorithmRun appears in the definition. The new-live mask must
eventually be certified exact for the full closure_(R.I(c+1))(Y). -/
noncomputable def kpt_candidate_residual_boring_crossing_cuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (j : Fin Q) : Finset Nat := by
  classical
  exact (Finset.range top).filter (fun cut =>
    (¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    ∧ cut < LevelTree.lev (newNode j)
    ∧ newLive cut j = true
    ∧ ¬ KptOldLiveImageAt φ oldLive cut j)

/-- Exact membership in the candidate residual crossing cut set. -/
theorem mem_kpt_candidate_residual_boring_crossing_cuts
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (j : Fin Q) (cut : Nat) :
    cut ∈ kpt_candidate_residual_boring_crossing_cuts
      family X top R newNode oldLive newLive φ j ↔
      cut < top ∧
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut ∧
      cut < LevelTree.lev (newNode j) ∧
      newLive cut j = true ∧
      ¬ KptOldLiveImageAt φ oldLive cut j := by
  classical
  simp only [kpt_candidate_residual_boring_crossing_cuts,
    Finset.mem_filter, Finset.mem_range]

/-- A SINGLE actual complete upper Kpt ancestor witness produces the
SAME dependent old/upper L+/E crossing pair in the genuine old
pre-cut closure. This bridge does not assume new-run existence, no
I2 fork or uniqueness of the old upper successor type. -/
theorem kpt_actual_run_upper_cover_gives_full_old_crossing_pair
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family) (cut : Nat)
    (p : PartialTypeWithE cut db du dd ×
      PartialTypeWithE (cut+1) db du dd)
    (hCovered : kpt_actual_run_node_upper_covered
      family X top R z cut)
    (hz : cut < LevelTree.lev z)
    (hOld : (⟨cut,p.1⟩ : RawPartialTypeNode db du dd) =
      (LevelTree.ancestor z cut (Nat.le_of_lt hz)).val)
    (hUpper : (⟨cut+1,p.2⟩ : RawPartialTypeNode db du dd) =
      (LevelTree.ancestor z (cut+1)
        (Nat.succ_le_iff.mpr hz)).val) :
    p ∈ FullPhysicalClosureCrossing family
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut := by
  obtain ⟨w,hwLive,hzCovered,hwCovered,hUpperEq⟩ := hCovered
  have hLowerEq :
      (LevelTree.ancestor z cut (Nat.le_of_lt hz)).val =
      (LevelTree.ancestor w cut (Nat.le_of_lt hwCovered)).val := by
    have hEq :=
      kpt_LevelTree_lower_ancestors_eq_of_higher_eq
        z w cut (cut+1) (by omega)
        (Nat.succ_le_iff.mpr hzCovered)
        (Nat.succ_le_iff.mpr hwCovered) hUpperEq
    exact congrArg Subtype.val hEq
  have hNextEq :
      (LevelTree.ancestor z (cut+1)
        (Nat.succ_le_iff.mpr hz)).val =
      (LevelTree.ancestor w (cut+1)
        (Nat.succ_le_iff.mpr hwCovered)).val :=
    congrArg Subtype.val hUpperEq
  exact ⟨w,hwLive,hwCovered,
    hOld.trans hLowerEq,hUpper.trans hNextEq⟩

/-- Given no NEW RUN, one old-run physical crossing cover at the
highest old-boring residual candidate cut suffices at ALL residual
cuts of that node. A matched old-LIVE name is self-covered.

Only the OLD AlgorithmRun closure monotonicity is used. -/
theorem kpt_actual_candidate_crossing_covered_of_max
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hOldSound : ∀ cut : Nat, cut < top →
      ∀ i : Fin P, oldLive cut i = true →
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X)
    (hMax : ∀ (j : Fin Q)
      (hNonempty : (kpt_candidate_residual_boring_crossing_cuts
        family X top R newNode oldLive newLive φ j).Nonempty),
      kpt_actual_run_node_upper_covered
        family X top R (newNode j)
        ((kpt_candidate_residual_boring_crossing_cuts
          family X top R newNode oldLive newLive φ j).max' hNonempty))
    (j : Fin Q) (cut : Nat)
    (hCut : cut < top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (hCross : cut < LevelTree.lev (newNode j))
    (hNewLive : newLive cut j = true) :
    kpt_actual_run_node_upper_covered
      family X top R (newNode j) cut := by
  classical
  by_cases hImage : KptOldLiveImageAt φ oldLive cut j
  · exact kpt_actual_old_live_image_upper_covered
      family X top R oldNode newNode oldLive φ
      hNodes hOldSound j cut hCut hCross hImage
  · let C := kpt_candidate_residual_boring_crossing_cuts
      family X top R newNode oldLive newLive φ j
    have hIn : cut ∈ C :=
      (mem_kpt_candidate_residual_boring_crossing_cuts
        family X top R newNode oldLive newLive φ j cut).mpr
        ⟨hCut,hBoring,hCross,hNewLive,hImage⟩
    have hNonempty : C.Nonempty := ⟨cut,hIn⟩
    have hMaxMem : C.max' hNonempty ∈ C :=
      Finset.max'_mem C hNonempty
    have hMaxData :=
      (mem_kpt_candidate_residual_boring_crossing_cuts
        family X top R newNode oldLive newLive φ j
        (C.max' hNonempty)).mp hMaxMem
    have hMaxCut : C.max' hNonempty < top := hMaxData.1
    have hLe : cut ≤ C.max' hNonempty :=
      Finset.le_max' C cut hIn
    have hAtMax : kpt_actual_run_node_upper_covered
        family X top R (newNode j) (C.max' hNonempty) :=
      hMax j hNonempty
    exact kpt_actual_run_node_upper_covered_mono_down
      family X top R (newNode j)
      cut (C.max' hNonempty) hLe hMaxCut hAtMax

/-- One certificate per finite candidate NEW physical node:
its sole terminal-level test plus one maximal residual complete
crossing-cover test. Both sources use the OLD R.I tails, so the
result constructs a new genuine AlgorithmRun rather than assuming it.

The hypotheses DO NOT establish these tests for the canonical
resolved-diary Henson construction or a uniform diary source index. -/
theorem kpt_transport_actualRun_of_candidate_residual_frontier
    {db du dd P Q : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (φ : Fin P → Fin Q)
    (hNodes : ∀ i : Fin P, newNode (φ i) = oldNode i)
    (hOldSound : ∀ cut : Nat, cut < top →
      ∀ i : Fin P, oldLive cut i = true →
      oldNode i ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X)
    (hNewExact : ∀ cut : Nat, cut < top →
      ∀ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y ↔
        ∃ j : Fin Q, newNode j = z ∧ newLive cut j = true)
    (hNoNewTerminal : ∀ (j : Fin Q),
      LevelTree.lev (newNode j) < top →
      (¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (LevelTree.lev (newNode j)+1)) X)
        (LevelTree.lev (newNode j))) →
      newLive (LevelTree.lev (newNode j)) j = false)
    (hMax : ∀ (j : Fin Q)
      (hNonempty : (kpt_candidate_residual_boring_crossing_cuts
        family X top R newNode oldLive newLive φ j).Nonempty),
      kpt_actual_run_node_upper_covered
        family X top R (newNode j)
        ((kpt_candidate_residual_boring_crossing_cuts
          family X top R newNode oldLive newLive φ j).max' hNonempty)) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F := by
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY top R
  intro cut hCut hBoring
  constructor
  · rintro ⟨z,hzNew,hLev⟩
    obtain ⟨j,hNode,hLive⟩ :=
      (hNewExact cut hCut z).mp hzNew
    have hNodeLev : LevelTree.lev (newNode j) = cut := by
      rw [hNode]
      exact hLev
    have hNoLive := hNoNewTerminal j (by omega) (by
      simpa only [hNodeLev] using hBoring)
    have hAtTerm : newLive (LevelTree.lev (newNode j)) j = true := by
      simpa only [hNodeLev] using hLive
    rw [hNoLive] at hAtTerm
    cases hAtTerm
  · intro p hpNew
    obtain ⟨z,hzNew,hCross,hOld,hUpper⟩ := hpNew
    obtain ⟨j,hNode,hLive⟩ :=
      (hNewExact cut hCut z).mp hzNew
    have hJCros : cut < LevelTree.lev (newNode j) := by
      rw [hNode]
      exact hCross
    have hCoveredJ :=
      kpt_actual_candidate_crossing_covered_of_max
        family X top R oldNode newNode oldLive newLive φ
        hNodes hOldSound hMax j cut hCut hBoring hJCros hLive
    have hCoveredZ : kpt_actual_run_node_upper_covered
        family X top R z cut := by
      simpa only [hNode] using hCoveredJ
    exact kpt_actual_run_upper_cover_gives_full_old_crossing_pair
      family X top R z cut p hCoveredZ hCross hOld hUpper

end Kk
