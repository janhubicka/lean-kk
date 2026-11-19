import Kk.TrackECandidateSourceResidualFrontier
import Kk.TrackDPreCutStageSource
import Mathlib.Tactic

/-!
# Track E E71: one maximal actual-original crossing test per source original

English-first mathematical proof and 22 adversarial checks:
docs/track_e_original_representative_max_frontier_english_audit_20261119.md

Unlike E69, we do NOT index the complete candidate Kpt meet/parameter
closure. The checked numerical-H+ stage representation assigns every
candidate source node z a REAL original coordinate v, in the TRUE
stage pool R.I(c+1), with z <= kptOriginal v. The entire complete
dependent old/upper L+/E crossing of z is then determined by the
same upper ancestor of that original v.

Thus ONE maximal old-boring eligible test PER actual original v,
plus the separate true terminal-I1 absence, suffices to construct
a genuine target AlgorithmRun with the exact old I and TOTAL F.
No new AlgorithmRun or finite auxiliary-source index is assumed.
The geometric maximal tests themselves remain application premises.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The true source cuts where a fixed physical original v actually
represents SOME new full candidate Kpt source node crossing the cut,
and the old complete physical Kpt AlgorithmRun is BORING there.
A stage-pool original alone need not be a live closure node. -/
noncomputable def kpt_candidate_original_boring_crossing_cuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin N) : Finset Nat := by
  classical
  exact (Finset.range top).filter (fun cut =>
    (¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut) ∧
    v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v))

/-- The exact finite original-stage candidate-cut membership test. -/
theorem mem_kpt_candidate_original_boring_crossing_cuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (v : Fin N) (cut : Nat) :
    cut ∈ kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v ↔
    cut < top ∧
    ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut ∧
    v ∈ hStageOriginals K k N U (R.I (cut+1)) ∧
    (∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) := by
  classical
  simp only [kpt_candidate_original_boring_crossing_cuts,
    Finset.mem_filter, Finset.mem_range]

/-- A closure node below an actual original shares that ORIGINAL's
complete upper Kpt ancestor at every cut crossed by the node.
Hence any physical OLD upper-ancestor witness for the original
immediately covers the node itself. The original does NOT have to
lie in the old or new pre-cut closure; only the OLD witness does.
No no-I2, source-index or positive-L projection hypotheses. -/
theorem kpt_actual_upper_cover_transfer_from_representing_original
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z original : AdmissibleKptNode family)
    (hBelow : z ≤ original)
    (cut : Nat) (hCross : cut < LevelTree.lev z)
    (hOriginalCovered : kpt_actual_run_node_upper_covered
      family X top R original cut) :
    kpt_actual_run_node_upper_covered
      family X top R z cut := by
  obtain ⟨w,hwLive,hOrigCross,hWCross,hOldUpperEq⟩ :=
    hOriginalCovered
  have hZNext : cut+1 ≤ LevelTree.lev z :=
    Nat.succ_le_iff.mpr hCross
  have hOrigNext : cut+1 ≤ LevelTree.lev original :=
    Nat.succ_le_iff.mpr hOrigCross
  have hZOriginalUpper :
      LevelTree.ancestor z (cut+1) hZNext =
        LevelTree.ancestor original (cut+1) hOrigNext := by
    exact LevelTree.eq_ancestor_of_le
      ((LevelTree.ancestor_le z (cut+1) hZNext).trans hBelow)
      (LevelTree.level_ancestor z (cut+1) hZNext)
      hOrigNext
  exact ⟨w,hwLive,hCross,hWCross,
    hZOriginalUpper.trans hOldUpperEq⟩

/-- The genuine candidate source needs at most one complete OLD
upper-Kpt-ancestor crossing test at the highest old-boring eligible
cut per actual original coordinate v: the checked stage-original
representation gives every new live crossing source z <= O_v,
G294 moves coverage DOWN across source cuts, and the level-tree
ancestor lemma transfers it from O_v to z.

No second target run, arbitrary final original pool, auxiliary
source enumeration or I2-functional crossing is assumed. -/
theorem finiteNumericH_oldRun_candidate_crossing_covered_of_original_max
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hMax : ∀ (v : Fin N)
      (hNonempty : (kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v).Nonempty),
      kpt_actual_run_node_upper_covered
        family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        ((kpt_candidate_original_boring_crossing_cuts
          family K k N hAvoid U X Y top R v).max' hNonempty))
    (cut : Nat) (hCut : cut < top)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (z : AdmissibleKptNode family)
    (hNew : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (cut+1)) Y)
    (hCross : cut < LevelTree.lev z) :
    kpt_actual_run_node_upper_covered
      family X top R z cut := by
  classical
  obtain ⟨v,hStage,hBelow⟩ :=
    finiteNumericH_stage_closure_represented_by_stage_originals
      family K k N hAvoid U Y hY (R.I (cut+1)) z hNew
  let C := kpt_candidate_original_boring_crossing_cuts
    family K k N hAvoid U X Y top R v
  have hIn : cut ∈ C :=
    (mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v cut).mpr
      ⟨hCut,hBoring,hStage,⟨z,hNew,hCross,hBelow⟩⟩
  have hNonempty : C.Nonempty := ⟨cut,hIn⟩
  have hMaxMem : C.max' hNonempty ∈ C :=
    Finset.max'_mem C hNonempty
  have hMaxCut : C.max' hNonempty < top :=
    ((mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v
      (C.max' hNonempty)).mp hMaxMem).1
  have hCutLe : cut ≤ C.max' hNonempty :=
    Finset.le_max' C cut hIn
  have hAtMax : kpt_actual_run_node_upper_covered
      family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v)
      (C.max' hNonempty) := hMax v hNonempty
  have hOriginalCovered : kpt_actual_run_node_upper_covered
      family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v) cut :=
    kpt_actual_run_node_upper_covered_mono_down
      family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v)
      cut (C.max' hNonempty) hCutLe hMaxCut hAtMax
  exact kpt_actual_upper_cover_transfer_from_representing_original
    family X top R z
    ((finiteNumericH K k N).kptOriginal family hAvoid v)
    hBelow cut hCross hOriginalCovered

/-- An entirely ORIGINAL-COORDINATE finite certificate for one genuine
old numerical-H+ AlgorithmRun to extend to the new seed set Y
without changing its selected levels I or its TOTAL monoid map F.

The only geometric obligations remaining are:
 (1) no full Kpt terminal in the candidate closure at OLD-boring cuts,
 (2) one actual old full upper-ancestor cover at the maximal
     old-boring eligible cut of each real numerical-H+ original.
No candidate Kpt source enumeration and no target run are assumed.

This conditional theorem is not a proof of the global resolved-diary
construction, uniform exceptional microevent bound or BRD upper bound. -/
theorem finiteNumericH_transport_actualRun_of_original_max_crossings
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericH K k N).L)
    (U : Finset (Fin N))
    (X Y : Set (AdmissibleKptNode family))
    (hXY : X ⊆ Y)
    (hY : Y ⊆ ambientPrefixPool family
      (finiteNumericH K k N) hAvoid (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hNoNewTerminal : ∀ cut : Nat, cut < top →
      ¬ SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family)
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) X) cut →
      ¬ KptI1AtCut family
        (SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (cut+1)) Y) cut)
    (hMax : ∀ (v : Fin N)
      (hNonempty : (kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v).Nonempty),
      kpt_actual_run_node_upper_covered
        family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        ((kpt_candidate_original_boring_crossing_cuts
          family K k N hAvoid U X Y top R v).max' hNonempty)) :
    ∃ RY : SMTree.Envelope.AlgorithmRun
        (normalizedKptSMTree family) Y top,
      RY.I = R.I ∧ RY.F = R.F := by
  apply kpt_transport_actualRun_of_boring_only_noNovelty
    family X Y hXY top R
  intro cut hCut hBoring
  constructor
  · intro hTerminal
    exact False.elim ((hNoNewTerminal cut hCut hBoring) hTerminal)
  · intro p hpNew
    obtain ⟨z,hNew,hCross,hOld,hUpper⟩ := hpNew
    have hZCovered :=
      finiteNumericH_oldRun_candidate_crossing_covered_of_original_max
        family K k N hAvoid U X Y hY top R hMax
        cut hCut hBoring z hNew hCross
    exact kpt_actual_run_upper_cover_gives_full_old_crossing_pair
      family X top R z cut p hZCovered hCross hOld hUpper

end Kk
