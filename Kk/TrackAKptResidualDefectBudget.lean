import Kk.PartialNumericCriticalGenerations
import Kk.TrackAGExceptionSelected
import Mathlib.Tactic

/-!
# Track A/G: residual dependent Kpt full-profile defect budget

English proof and adversarial audit committed BEFORE Lean:
  docs/track_a_g_residual_kpt_profile_defect_budget_english_audit_20261122.md

We separate genuine ordinary-L Henson critical generations C(E,b,j)
from cuts outside C at which TWO actual same-top Kpt AlgorithmRuns
have different I1 terminal or COMPLETE dependent old/upper L+/E
physical crossing profiles at their actual stagewise pre-cut closures.

The resulting defect-count bound is unconditional bookkeeping for
those actual scans; it does NOT construct the Kpt runs from E or prove
that a proposed diary makes all dependent defects vanish. Neither a
common source orbit nor the global BRD theorem is claimed.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The FINITE set of actual dependent-Kpt full-profile defects at
cuts outside a specified ordinary exceptional set. It is a logically
defined Finset; no effective finite Kpt source indexing is asserted.
The tests use BOTH actual pre-cut closures, not one common shadow. -/
noncomputable def kptOffExceptionFullProfileDefects
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (ordinary : Finset Nat) : Finset Nat := by
  classical
  exact (Finset.range top).filter (fun cut =>
    cut ∉ ordinary ∧ ¬
      ((KptI1AtCut family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X) cut ↔
        KptI1AtCut family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RY.I (cut+1)) Y) cut) ∧
       FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X) cut =
        FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RY.I (cut+1)) Y) cut))

/-- At any actual scanned cut outside BOTH the named ordinary
exceptions and the residual profile defects, the full dependent
terminal/crossing profiles literally agree. This follows directly
from the exact definition of the defect Finset, with no diary axiom. -/
theorem kpt_full_profiles_eq_of_not_mem_off_exception_defects
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (ordinary : Finset Nat)
    (cut : Nat) (hCut : cut < top)
    (hOrd : cut ∉ ordinary)
    (hDef : cut ∉ kptOffExceptionFullProfileDefects
      family X Y top RX RY ordinary) :
    (KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut ↔
      KptI1AtCut family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut) ∧
    FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RX.I (cut+1)) X) cut =
      FullPhysicalClosureCrossing family
        (SMTree.Envelope.closure (admissibleKptSTree family)
          (RY.I (cut+1)) Y) cut := by
  classical
  by_contra hBad
  apply hDef
  unfold kptOffExceptionFullProfileDefects
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hCut, ⟨hOrd, hBad⟩⟩

/-- GENERAL ACTUAL-SOURCE ledger: the number of final selected-level
disagreements of two different-seed genuine Kpt AlgorithmRuns is at
most the number of supplied ordinary exceptions PLUS the number of
remaining complete dependent Kpt-profile defects.
This does not bound either run's total interesting levels. -/
theorem kpt_actual_runs_selected_disagreement_le_exception_plus_defects
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X Y : Set (AdmissibleKptNode family))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) Y top)
    (ordinary : Finset Nat) :
    ((RX.I 0 \ RY.I 0) ∪ (RY.I 0 \ RX.I 0)).ncard ≤
      ordinary.card +
        (kptOffExceptionFullProfileDefects
          family X Y top RX RY ordinary).card := by
  classical
  let defects :=
    kptOffExceptionFullProfileDefects
      family X Y top RX RY ordinary
  let exceptional : Finset Nat := ordinary ∪ defects
  have hGood (cut : Nat) (hCut : cut < top)
      (hOutside : cut ∉ (exceptional : Set Nat)) :
      (KptI1AtCut family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X) cut ↔
        KptI1AtCut family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RY.I (cut+1)) Y) cut) ∧
      FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RX.I (cut+1)) X) cut =
        FullPhysicalClosureCrossing family
          (SMTree.Envelope.closure (admissibleKptSTree family)
            (RY.I (cut+1)) Y) cut := by
    have hOrd : cut ∉ ordinary := by
      intro h
      exact hOutside (Finset.mem_union.mpr (Or.inl h))
    have hDef : cut ∉ defects := by
      intro h
      exact hOutside (Finset.mem_union.mpr (Or.inr h))
    exact kpt_full_profiles_eq_of_not_mem_off_exception_defects
      family X Y top RX RY ordinary cut hCut hOrd hDef
  have hSource :=
    kpt_actual_runs_selected_disagreement_card_le_of_full_profiles
      family X Y top RX RY exceptional
      (fun cut hCut hOutside => (hGood cut hCut hOutside).1)
      (fun cut hCut hOutside => (hGood cut hCut hOutside).2)
  have hCard : exceptional.card ≤ ordinary.card + defects.card :=
    Finset.card_union_le ordinary defects
  exact hSource.trans hCard

/-- SHARP HENSON ORDINARY-L PLUS EXACT DEPENDENT-KPT DEFECT BUDGET.
The ordinary critical-generation set contributes at most ell-2.
The residual term counts ACTUAL full source profile mismatches
outside those critical cuts, on the same aligned scan top.
No diary-to-profile comparison or relation between the graph E and
the two chosen source seed sets is constructed by this theorem. -/
theorem trackA_henson_kpt_selected_disagreement_le_sharp_plus_defects
    {d : Nat} (E : Nat → Nat → Bool)
    (ell : Nat) (hell : 2 ≤ ell)
    (hAvoid : ∀ bad, bad ∈ hensonForbiddenFamily ell hell →
      bad.Avoids (normalizedGraphModel E))
    (b : Nat) (j : Fin d → Nat) (hj : ∀ t, b < j t)
    (X Y : Set (AdmissibleKptNode
      (hensonForbiddenFamily ell hell)))
    (top : Nat)
    (RX : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) X top)
    (RY : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (hensonForbiddenFamily ell hell)) Y top) :
    ((RX.I 0 \ RY.I 0) ∪ (RY.I 0 \ RX.I 0)).ncard ≤
      ell-2 +
        (kptOffExceptionFullProfileDefects
          (hensonForbiddenFamily ell hell) X Y top RX RY
          (trackACriticalGenerations ell E b j)).card := by
  have hGeneral :=
    kpt_actual_runs_selected_disagreement_le_exception_plus_defects
      (hensonForbiddenFamily ell hell) X Y top RX RY
      (trackACriticalGenerations ell E b j)
  have hOrd :=
    trackA_henson_critical_generation_card_le
      E ell hell hAvoid b j hj
  omega

#print axioms Kk.kpt_full_profiles_eq_of_not_mem_off_exception_defects
#print axioms Kk.kpt_actual_runs_selected_disagreement_le_exception_plus_defects
#print axioms Kk.trackA_henson_kpt_selected_disagreement_le_sharp_plus_defects

end Kk
