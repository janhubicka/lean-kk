import Kk.NumericHStructuralCutClassifier
import SuccessorTree.V10.I3AlgorithmRunSharp
import Mathlib.Tactic

/-!
# Track C/D: actual AlgorithmRun I3 from finite complete Kpt structural tests

English-first proof and 15 hostile checks:
  docs/track_c_indexed_i3_failure_english_audit.md

At a POSITIVE genuinely selected level, the algorithm's interestingness
plus absence of both literal I1 and I2 gives failed corrected B3 by the
already checked successor-tree numerical H+ I3 theorem.

We discharge those two full-closure structural exclusions from the
finite, ACTIVE, complete-L+ Kpt index of Track C. No selected-shadow
projection, fake E on a separate L-only age witness, or common orbit.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- A TRUE finite numerical H+ AlgorithmRun selected positive cut
with no ACTIVE structural I1-level node and no ACTIVE old-equal/
upper-different full-L+ fork has FAILED canonical full corrected B3.

The complete finite Kpt source, its true per-cut mask, physical
original-prefix seed pool, top/root seed and run interestingness
are all explicit. The result is not a nonselected-cut statement
nor a global resolved-copy characterization. -/
theorem finiteNumericH_run_no_indexed_structural_event_fails_full_B3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X)
    (ell : Nat) (hPos : 0 < ell) (hLt : ell < top)
    (hN : ell < N) (hSelected : ell ∈ R.I 0)
    (hNoActiveI1 : ¬ ∃ i : Fin params.card,
      presentAt ell i = true ∧
      LevelTree.lev (params.equivFin.symm i).val = ell)
    (hNoActiveFork : ¬ ∃ i j : Fin params.card,
      presentAt ell i = true ∧ presentAt ell j = true ∧
      ell < LevelTree.lev (params.equivFin.symm i).val ∧
      ell < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val ell =
        kptFullOldAtCut (params.equivFin.symm j).val ell ∧
      kptFullUpperAtCut (params.equivFin.symm i).val ell ≠
        kptFullUpperAtCut (params.equivFin.symm j).val ell) :
    ¬ (selectedStagePoolPrescribedData
       (finiteNumericH K k N) ell
       (hOriginalName (hStageOriginals K k N U (R.I 0)))
       (closureSelectedOriginal family (finiteNumericH K k N)
         (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
         (hOriginalName (hStageOriginals K k N U (R.I 0)))
         (SMTree.Envelope.closure (admissibleKptSTree family)
           (R.I (ell+1)) X) ell)).CorrectedB3 family := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (ell+1)) X
  have hNoStruct :
      ¬ (KptI1AtCut family Z ell ∨ KptI2MeetAtCut family Z ell) := by
    intro hEvent
    have hIndexed :=
      (finiteNumericH_run_structural_I1I2_iff_active_node_or_fork
        family K k N hAvoidA (U : Set (Fin N))
        X hX top R params hParams presentAt hPresent ell hLt).mp hEvent
    rcases hIndexed with hI1 | hFork
    · exact hNoActiveI1 hI1
    · exact hNoActiveFork hFork
  have hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = ell := by
    intro hI1
    exact hNoStruct (Or.inl hI1)
  have hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell := by
    intro hI2
    exact hNoStruct (Or.inr hI2)
  exact numericH_algorithmRun_I3_stage_failedB3
    family K hCarrier hAvoidK k N U X hX
    top R hTop ell hPos hLt hN hSelected hNoI1 hNoI2

/-- Contrapositive: if the genuine selected full-source B3 age test
PASSES, then the complete active finite Kpt index must contain
a structural I1-level node OR a full old-equal/upper-different fork.

No marked-only B3 test is substituted for the full source. -/
theorem finiteNumericH_run_selected_full_B3_implies_indexed_I1_or_I2
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (params : Finset (AdmissibleKptNode family))
    (hParams : ∀ z : AdmissibleKptNode family,
      z ∈ params ↔
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X)
    (presentAt : Nat → Fin params.card → Bool)
    (hPresent : ∀ cut : Nat, ∀ i : Fin params.card,
      presentAt cut i = true ↔
        (params.equivFin.symm i).val ∈
          SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (cut+1)) X)
    (ell : Nat) (hPos : 0 < ell) (hLt : ell < top)
    (hN : ell < N) (hSelected : ell ∈ R.I 0)
    (hB3 :
      (selectedStagePoolPrescribedData
       (finiteNumericH K k N) ell
       (hOriginalName (hStageOriginals K k N U (R.I 0)))
       (closureSelectedOriginal family (finiteNumericH K k N)
         (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
         (hOriginalName (hStageOriginals K k N U (R.I 0)))
         (SMTree.Envelope.closure (admissibleKptSTree family)
           (R.I (ell+1)) X) ell)).CorrectedB3 family) :
    (∃ i : Fin params.card,
      presentAt ell i = true ∧
      LevelTree.lev (params.equivFin.symm i).val = ell) ∨
    (∃ i j : Fin params.card,
      presentAt ell i = true ∧ presentAt ell j = true ∧
      ell < LevelTree.lev (params.equivFin.symm i).val ∧
      ell < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val ell =
        kptFullOldAtCut (params.equivFin.symm j).val ell ∧
      kptFullUpperAtCut (params.equivFin.symm i).val ell ≠
        kptFullUpperAtCut (params.equivFin.symm j).val ell) := by
  classical
  by_contra hNone
  have hNoI1 : ¬ ∃ i : Fin params.card,
      presentAt ell i = true ∧
      LevelTree.lev (params.equivFin.symm i).val = ell := by
    intro h
    exact hNone (Or.inl h)
  have hNoFork : ¬ ∃ i j : Fin params.card,
      presentAt ell i = true ∧ presentAt ell j = true ∧
      ell < LevelTree.lev (params.equivFin.symm i).val ∧
      ell < LevelTree.lev (params.equivFin.symm j).val ∧
      kptFullOldAtCut (params.equivFin.symm i).val ell =
        kptFullOldAtCut (params.equivFin.symm j).val ell ∧
      kptFullUpperAtCut (params.equivFin.symm i).val ell ≠
        kptFullUpperAtCut (params.equivFin.symm j).val ell := by
    intro h
    exact hNone (Or.inr h)
  exact
    (finiteNumericH_run_no_indexed_structural_event_fails_full_B3
      family K hCarrier hAvoidK k N U X hX top R hTop
      params hParams presentAt hPresent ell hPos hLt hN hSelected
      hNoI1 hNoFork) hB3

#print axioms Kk.finiteNumericH_run_no_indexed_structural_event_fails_full_B3
#print axioms Kk.finiteNumericH_run_selected_full_B3_implies_indexed_I1_or_I2

end Kk
