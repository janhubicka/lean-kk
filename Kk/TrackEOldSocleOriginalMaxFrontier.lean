import Kk.TrackEOriginalRepresentativeMaxFrontier
import Mathlib.Tactic

/-!
# Track E E79: one maximal COMPLETE OLD Kpt prefix test per physical original

English proof and 20 hostile checks committed FIRST:
docs/track_e_old_socle_original_max_frontier_english_audit_20261120.md

The E72/E78 zero ordinary-L geometric test requires matching only
the COMPLETE OLD Kpt ancestor, rather than the assigned upper L+/E
successor type. In a genuine old AlgorithmRun this exact old-prefix
coverage persists DOWNWARD: the physical old witness remains in the
true pre-cut closure and matching high ancestors restrict to low.

Therefore, for any finite set of eligible source cuts (which need
not be an interval), ONE complete old-prefix test at the MAXIMAL
cut is equivalent to tests at ALL such cuts. Specialize to the
actual E71 physical-original crossing support intersected with
an arbitrary Allowed mask, e.g. positive even-real zero stages.

This does NOT show any maximal OLD source prefix actually exists
in the resolved numerical-H+ construction, or bound N in a diary.
Auxiliary K4 E/q2 cuts remain visible when eligible.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A physical COMPLETE OLD Kpt socle witness for a source node z
at literal normalized source cut c. The original z need not be a
member of either pre-cut closure: it may be a genuine numerical-H+
original representing some candidate auxiliary new-source node.

The OLD witness w must be in the REAL source closure given by
the genuine old AlgorithmRun's R.I(c+1) tail, and both nodes
must cross the cut. The equality retains ALL dependent L+/E
old-ancestor data; no positive-L-only projection is allowed. -/
def KptActualOldSocleCoveredAt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family) (cut : Nat) : Prop :=
  ∃ w : AdmissibleKptNode family,
    w ∈ SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (cut+1)) X ∧
    ∃ (hZ : cut < LevelTree.lev z)
      (hW : cut < LevelTree.lev w),
      LevelTree.ancestor z cut (Nat.le_of_lt hZ) =
        LevelTree.ancestor w cut (Nat.le_of_lt hW)

/-- Genuine OLD Kpt socle coverage persists toward SMALLER
source cuts. The SAME physical old witness w survives because
the genuine old pre-cut source is downward monotone; equality
of high literal Kpt ancestors restricts to lower ones.

The statement is false without genuine old-run closure-tail
monotonicity and is NOT about unrelated per-cut Boolean masks. -/
theorem kpt_actual_old_socle_covered_mono_down
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (low high : Nat)
    (hLe : low ≤ high) (hHigh : high < top)
    (hCovered : KptActualOldSocleCoveredAt
      family X top R z high) :
    KptActualOldSocleCoveredAt family X top R z low := by
  obtain ⟨w,hWLive,hZHigh,hWHigh,hAncestorHigh⟩ := hCovered
  have hZLow : low < LevelTree.lev z := by omega
  have hWLow : low < LevelTree.lev w := by omega
  refine ⟨w, ?_, hZLow,hWLow, ?_⟩
  · exact (kpt_actual_run_preCut_source_mono_down
      family X top low high R hLe hHigh) hWLive
  · exact kpt_LevelTree_lower_ancestors_eq_of_higher_eq
      z w low high hLe
      (Nat.le_of_lt hZHigh)
      (Nat.le_of_lt hWHigh) hAncestorHigh

/-- A finite, possibly disconnected family S of genuine source
cuts below oldTop has ALL complete old-prefix matches for z
if and only if the HIGHEST cut in S has a match. No interval
hypothesis on S is needed. At most one witness check per fixed
z, not a bound on how many cuts may be covered. -/
theorem kpt_actual_old_socle_all_cuts_iff_max
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (z : AdmissibleKptNode family)
    (S : Finset Nat)
    (hCuts : ∀ cut : Nat, cut ∈ S → cut < top)
    (hNonempty : S.Nonempty) :
    (∀ cut : Nat, cut ∈ S →
      KptActualOldSocleCoveredAt family X top R z cut) ↔
    KptActualOldSocleCoveredAt
      family X top R z (S.max' hNonempty) := by
  constructor
  · intro hAll
    exact hAll (S.max' hNonempty)
      (Finset.max'_mem S hNonempty)
  · intro hMax cut hCut
    exact kpt_actual_old_socle_covered_mono_down
      family X top R z cut (S.max' hNonempty)
      (Finset.le_max' S cut hCut)
      (hCuts (S.max' hNonempty) (Finset.max'_mem S hNonempty))
      hMax

/-- Restrict E71's TRUE old-boring/new-live physical original
crossing cut support to ANY externally chosen set Allowed.
Allowed can mean exactly the positive even-real ZERO-column
stage cuts relevant to E72/E77; no assumption that it is an
interval, nor that all source cuts are zero-column. -/
noncomputable def kpt_actual_original_socle_allowed_cuts
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
    (Allowed : Set Nat) (v : Fin N) : Finset Nat := by
  classical
  exact (kpt_candidate_original_boring_crossing_cuts
    family K k N hAvoid U X Y top R v).filter
      (fun cut => cut ∈ Allowed)

/-- Exact membership in E79's restricted actual original source
cut family, preserving E71's genuine stage/live/old-boring tests.
The new filter is only the caller's Allowed source-cut mask. -/
theorem mem_kpt_actual_original_socle_allowed_cuts
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
    (Allowed : Set Nat) (v : Fin N) (cut : Nat) :
    cut ∈ kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v ↔
    cut ∈ kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v ∧ cut ∈ Allowed := by
  classical
  simp only [kpt_actual_original_socle_allowed_cuts,
    Finset.mem_filter]

/-- The E79 maximal OLD Kpt-socle certificate for ONE actual
numerical-H+ original O_v, over precisely the eligible
old-boring source cuts intersected with Allowed.

This is strictly a COMPLETE OLD prefix test; upper successor
L+/E equality follows at genuine zero-column cuts only by
the distinct verified E72 theorem. -/
theorem kpt_actual_original_socle_allowed_cuts_iff_max
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
    (Allowed : Set Nat) (v : Fin N)
    (hNonempty :
      (kpt_actual_original_socle_allowed_cuts
        family K k N hAvoid U X Y top R Allowed v).Nonempty) :
    (∀ cut : Nat,
      cut ∈ kpt_actual_original_socle_allowed_cuts
        family K k N hAvoid U X Y top R Allowed v →
      KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v) cut) ↔
    KptActualOldSocleCoveredAt family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v)
      ((kpt_actual_original_socle_allowed_cuts
        family K k N hAvoid U X Y top R Allowed v).max' hNonempty) := by
  apply kpt_actual_old_socle_all_cuts_iff_max
    family X top R
    ((finiteNumericH K k N).kptOriginal family hAvoid v)
    (kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v) ?_ hNonempty
  intro cut hCut
  have hBase :
      cut ∈ kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v :=
    (mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mp hCut |>.1
  exact ((mem_kpt_candidate_original_boring_crossing_cuts
    family K k N hAvoid U X Y top R v cut).mp hBase).1

/-- APPLICATION-FACING one-test-per-actual-ORIGINAL consequence:
given one OLD physical Kpt prefix match at the maximal eligible
cut of each original, a physical original that represents any
new-live crossing at an arbitrary lower Allowed old-boring cut
automatically has an OLD-LIVE matching complete Kpt prefix.

No upper type, new run, auxiliary source-node index or uniform
number of diary events is asserted. -/
theorem kpt_actual_original_socle_covered_of_all_allowed_max
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
    (Allowed : Set Nat)
    (hMax : ∀ v : Fin N,
      ∀ (hNonempty :
        (kpt_actual_original_socle_allowed_cuts
          family K k N hAvoid U X Y top R Allowed v).Nonempty),
      KptActualOldSocleCoveredAt family X top R
        ((finiteNumericH K k N).kptOriginal family hAvoid v)
        ((kpt_actual_original_socle_allowed_cuts
          family K k N hAvoid U X Y top R Allowed v).max' hNonempty))
    (v : Fin N) (cut : Nat)
    (hCut : cut < top)
    (hAllowed : cut ∈ Allowed)
    (hBoring : ¬ SMTree.Envelope.IsInterestingAt
      (normalizedKptSMTree family)
      (SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) X) cut)
    (hStage : v ∈ hStageOriginals K k N U (R.I (cut+1)))
    (hRep : ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (cut+1)) Y ∧
      cut < LevelTree.lev z ∧
      z ≤ (finiteNumericH K k N).kptOriginal family hAvoid v) :
    KptActualOldSocleCoveredAt family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v) cut := by
  classical
  let S := kpt_actual_original_socle_allowed_cuts
    family K k N hAvoid U X Y top R Allowed v
  have hInBase :
      cut ∈ kpt_candidate_original_boring_crossing_cuts
        family K k N hAvoid U X Y top R v :=
    (mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v cut).mpr
      ⟨hCut,hBoring,hStage,hRep⟩
  have hIn : cut ∈ S :=
    (mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v cut).mpr
      ⟨hInBase,hAllowed⟩
  have hNonempty : S.Nonempty := ⟨cut,hIn⟩
  have hAtMax : KptActualOldSocleCoveredAt family X top R
      ((finiteNumericH K k N).kptOriginal family hAvoid v)
      (S.max' hNonempty) := hMax v hNonempty
  have hMaxMem : S.max' hNonempty ∈ S :=
    Finset.max'_mem S hNonempty
  have hBaseMax :
      S.max' hNonempty ∈
        kpt_candidate_original_boring_crossing_cuts
          family K k N hAvoid U X Y top R v :=
    ((mem_kpt_actual_original_socle_allowed_cuts
      family K k N hAvoid U X Y top R Allowed v _).mp hMaxMem).1
  have hMaxCut : S.max' hNonempty < top :=
    ((mem_kpt_candidate_original_boring_crossing_cuts
      family K k N hAvoid U X Y top R v _).mp hBaseMax).1
  exact kpt_actual_old_socle_covered_mono_down
    family X top R
    ((finiteNumericH K k N).kptOriginal family hAvoid v)
    cut (S.max' hNonempty)
    (Finset.le_max' S cut hIn) hMaxCut hAtMax

end Kk
