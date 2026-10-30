import Kk.AlgorithmRunTwoB3Selection
import Kk.K4ActualAlgorithmRunCut22
import Kk.K4NumericalHCut10Transfer
import Mathlib.Tactic

/-!
# The concrete numerical-H K4 gadget forces BOTH selected cuts

The upper original x=38 forces cut22 by its actual single-upper B3
failure; the true AlgorithmRun closure then contains q2=22 at cut10.
The full ambient cut10 L-only continuation with q2,x,x is a failed
two-upper B3 age test. The generic two-ambient-source I3 theorem
therefore forces cut10 as well.

These are ACTUAL AlgorithmRun selections, not abstract graph-age
shadows or a claim about minimal labelled diary/source equivalence.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The auxiliary q2 original at numerical address 22 has exact
E-free level 11, hence is eligible at cut10. -/
theorem k4GadgetH_q2_freeLevel_eq_11 :
    k4GadgetH.freeLevel 22 = 11 := by
  have h := finiteNumericH_next_generation_one_freeLevel
    (normalizedGraphModel k4FourOriginalEdge) 4 40 1
    (by decide) (by decide)
  have h22 : hPosition 4 (1+1) 1 = 22 := by decide
  have h10 : hPosition 4 1 0 = 10 := by decide
  rw [h22, h10] at h
  exact h

/-- Every genuine Algorithm 5.4 run seeded by the concrete top
original 38 and scanning past 22 also SELECTS cut10, by the
actual mixed q2,x,x B3 obstruction over the full old socle. -/
theorem k4Gadget_algorithmRun_selects_cut10
    (X : Set (AdmissibleKptNode k4GadgetFamily))
    (hSeed : k4GadgetH.kptOriginal
      k4GadgetFamily k4GadgetH_avoids
      (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈ X)
    (ell : Nat) (hEll : 22 < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree k4GadgetFamily) X ell) :
    10 ∈ R.I 10 := by
  have hFreeQ : 10 < k4GadgetH.freeLevel 22 := by
    rw [k4GadgetH_q2_freeLevel_eq_11]
    decide
  have hFreeX : 10 < k4GadgetH.freeLevel 38 := by
    have hX := k4GadgetH_top_freeLevel_above22
    omega
  have hCq :=
    k4Gadget_algorithmRun_q2_in_cut10_closure X hSeed ell hEll R
  have hCx :
      k4GadgetH.kptOriginal
        k4GadgetFamily k4GadgetH_avoids
        (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈
      SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree k4GadgetFamily) (R.I 11) X :=
    (SuccessorTree.SMTree.Envelope.subset_closure
      (admissibleKptSTree k4GadgetFamily) (R.I 11) X) hSeed
  exact algorithmRun_selects_actual_failed_two_upper_B3
    k4GadgetFamily k4GadgetH k4GadgetH_avoids
    (⟨22, by change 22 < 40; decide⟩ : Fin k4GadgetH.size)
    (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size)
    10 (by decide) hFreeQ hFreeX
    k4H_actual_cut10_twoUpper_B3_failure
    X ell (by omega) R hCq hCx

/-- Both cuts of this concrete K4 auxiliary clique gadget are
unavoidable selections in every genuine seeded AlgorithmRun.
This does NOT by itself decide the globally resolved diary count. -/
theorem k4Gadget_algorithmRun_selects_cuts10_22
    (X : Set (AdmissibleKptNode k4GadgetFamily))
    (hSeed : k4GadgetH.kptOriginal
      k4GadgetFamily k4GadgetH_avoids
      (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈ X)
    (ell : Nat) (hEll : 22 < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree k4GadgetFamily) X ell) :
    10 ∈ R.I 10 ∧ 22 ∈ R.I 22 :=
  ⟨k4Gadget_algorithmRun_selects_cut10 X hSeed ell hEll R,
   k4Gadget_algorithmRun_selects_cut22 X hSeed ell hEll R⟩

end Kk
