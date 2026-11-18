import Kk.TrackGCrossingFrontier
import Kk.TrackENumericResidualTwoClass
import Mathlib.Tactic

/-!
# Track E E67: one maximal eligible complete crossing check per Kpt node

For a fixed actual admissible Kpt source node z in a pair of genuine
AlgorithmRuns, let eligible cuts be old-boring, off-plan, NEW-LIVE
crossing cuts inside the common source scan range. This is a finite
Finset of literal SOURCE coordinates.

Actual old complete old/upper L+ crossing coverage of the SAME node
is downward monotone by the already checked G294 theorem. Therefore
checking one maximal eligible cut is BOTH necessary and sufficient
for coverage at ALL eligible cuts for that node. Failure at ANY
eligible cut implies failure at that maximal eligible cut.

This does not bound the number of nodes or the number of bad cuts
when the maximal test fails; terminals require a separate I1 test.
English-first proof and 20 hostile cases:
docs/track_e_max_eligible_crossing_frontier_english_audit_20261118.md
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The exact finite family of old-boring OFF-PLAN source cuts
where one actual NEW pre-cut Kpt node is live and crosses.
The cutoff uses the COMMON scan range, not numerical target gaps.
No source-coordinate normalization between distinct diary
occurrences is asserted. -/
noncomputable def kpt_actual_offplan_node_eligible_crossing_cuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (z : AdmissibleKptNode family) : Finset Nat := by
  classical
  exact (Finset.range (min oldTop newTop)).filter
    (fun cut => cut ∉ Rold.I cut ∧ cut ∉ Allowed ∧
      cut < LevelTree.lev z ∧
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (cut+1)) Y)

/-- Membership lists ALL true source conditions. In particular,
cut-level terminals are deliberately excluded by cut<lev(z). -/
theorem mem_kpt_actual_offplan_node_eligible_crossing_cuts
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (z : AdmissibleKptNode family)
    (cut : Nat) :
    cut ∈ kpt_actual_offplan_node_eligible_crossing_cuts
      family X Y oldTop newTop Rold Rnew Allowed z ↔
    cut < min oldTop newTop ∧
      cut ∉ Rold.I cut ∧ cut ∉ Allowed ∧
      cut < LevelTree.lev z ∧
      z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
        (Rnew.I (cut+1)) Y := by
  classical
  simp only [kpt_actual_offplan_node_eligible_crossing_cuts,
    Finset.mem_filter, Finset.mem_range]

/-- If the eligible-cut set for ONE z is nonempty, complete
same-node old/upper dependent L+ crossing coverage at its
MAXIMAL eligible source cut is equivalent to coverage at EVERY
eligible source cut. The checked G294 lemma restricts the
literal actual OLD crossing witness down through the cuts.

The eligible set may be disconnected by interesting/allowed
cuts; this iff does not assume interval structure. -/
theorem kpt_actual_eligible_crossings_all_covered_iff_max
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (z : AdmissibleKptNode family)
    (hNonempty :
      (kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop Rold Rnew Allowed z).Nonempty) :
    (∀ cut : Nat,
      cut ∈ kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop Rold Rnew Allowed z →
      kpt_actual_run_node_upper_covered
        family X oldTop Rold z cut) ↔
    kpt_actual_run_node_upper_covered
      family X oldTop Rold z
        ((kpt_actual_offplan_node_eligible_crossing_cuts
          family X Y oldTop newTop Rold Rnew Allowed z).max' hNonempty) := by
  let C := kpt_actual_offplan_node_eligible_crossing_cuts
    family X Y oldTop newTop Rold Rnew Allowed z
  change (∀ cut : Nat, cut ∈ C →
      kpt_actual_run_node_upper_covered family X oldTop Rold z cut) ↔
    kpt_actual_run_node_upper_covered family X oldTop Rold z
      (C.max' hNonempty)
  constructor
  · intro hAll
    exact hAll _ (Finset.max'_mem C hNonempty)
  · intro hMax cut hCut
    have hMaxMem : C.max' hNonempty ∈ C :=
      Finset.max'_mem C hNonempty
    have hMaxConditions :=
      (mem_kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop Rold Rnew Allowed z
        (C.max' hNonempty)).mp hMaxMem
    have hMaxWithin :
        C.max' hNonempty < min oldTop newTop :=
      hMaxConditions.1
    have hMaxOld : C.max' hNonempty < oldTop :=
      lt_of_lt_of_le hMaxWithin (Nat.min_le_left oldTop newTop)
    have hCutLe : cut ≤ C.max' hNonempty :=
      Finset.le_max' C cut hCut
    exact kpt_actual_run_node_upper_covered_mono_down
      family X oldTop Rold z cut (C.max' hNonempty)
      hCutLe hMaxOld hMax

/-- Any missing COMPLETE crossing pair at an old-boring off-plan
eligible cut for z necessarily remains missing at the HIGHEST
eligible cut for that same physical z (and conversely).
This is a single-frontier TEST per node, not a diary-uniform
bound on nodes, interval length, or physical microcuts. -/
theorem kpt_actual_eligible_missing_crossing_iff_max
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (oldTop newTop : Nat)
    (Rold : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X oldTop)
    (Rnew : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y newTop)
    (Allowed : Set Nat)
    (z : AdmissibleKptNode family)
    (hNonempty :
      (kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop Rold Rnew Allowed z).Nonempty) :
    (∃ cut : Nat,
      cut ∈ kpt_actual_offplan_node_eligible_crossing_cuts
        family X Y oldTop newTop Rold Rnew Allowed z ∧
      ¬ kpt_actual_run_node_upper_covered
        family X oldTop Rold z cut) ↔
    ¬ kpt_actual_run_node_upper_covered
      family X oldTop Rold z
        ((kpt_actual_offplan_node_eligible_crossing_cuts
          family X Y oldTop newTop Rold Rnew Allowed z).max' hNonempty) := by
  let C := kpt_actual_offplan_node_eligible_crossing_cuts
    family X Y oldTop newTop Rold Rnew Allowed z
  change (∃ cut : Nat, cut ∈ C ∧
      ¬ kpt_actual_run_node_upper_covered
        family X oldTop Rold z cut) ↔
      ¬ kpt_actual_run_node_upper_covered family X oldTop Rold z
        (C.max' hNonempty)
  constructor
  · rintro ⟨cut,hCut,hNotCovered⟩ hMaxCovered
    have hAll :=
      (kpt_actual_eligible_crossings_all_covered_iff_max
        family X Y oldTop newTop Rold Rnew Allowed z
        hNonempty).mpr hMaxCovered
    exact hNotCovered (hAll cut hCut)
  · intro hNotMax
    exact ⟨C.max' hNonempty, Finset.max'_mem C hNonempty,
      hNotMax⟩

end Kk
