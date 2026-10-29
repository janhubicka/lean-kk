import Kk.AlgorithmRunSingleB3Selection
import Kk.K4NumericalHB3Transfer
import Kk.B3GadgetClosureParameter
import Mathlib.Tactic

/-!
# The genuine numerical-H K4 run selects the second gadget cut

The author's concrete K4 auxiliary-clique example has original indices
p=0, q1=1, q2=2, x=3 and numerical H height k=4, finite bound N=40.
The actual top selected original is at coordinate 38 (free level 29).
The two reserved gadget originals are at coordinates 10 and 22.

All relevant premises are now checked in Lean:
* the actual finite numerical H avoids the normalized K4 family;
* the complete single-upper-type B3 test fails at cut 22 for
  original 38, including the ENTIRE 23-vertex initial L socle;
* every genuine AlgorithmRun which contains that seed must select
  cut 22 (generic theorem in AlgorithmRunSingleB3Selection);
* selection of 22 forces the true Kpt original at 22 into the
  parameter closure scanned at cut 10.

No graph-age-shadow projection, invented E on age witnesses or
choice of f_i on an enlarged ambient pool is used.

This formalizes a concrete obstruction to the proposed argument
that the first of two reserved auxiliary clique vertices is always
boring. It does NOT alone establish the actual full corrected-B3
failure at cut 10 (where the upper q2 name is now selected), nor
that the same configuration occurs in every canonical resolved
copy, nor the equality of common labelled diary sources.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- The normalized loop/asymmetry/clique forbidden family of K4. -/
abbrev k4GadgetFamily : List (NormalizedForbidden 1 0 1) :=
  hensonForbiddenFamily 4 (by decide)

/-- The concrete four-original finite H+ model. -/
noncomputable abbrev k4GadgetH : EnumeratedPartialStructure 1 0 1 :=
  finiteNumericH (normalizedGraphModel k4FourOriginalEdge) 4 40

/-- The actual finite numerical H built from the K4-free base
omits every member of the indexed normalized forbidden family. -/
theorem k4GadgetH_avoids :
    ∀ bad, bad ∈ k4GadgetFamily →
      bad.Avoids k4GadgetH.L := by
  have hBase :
      ∀ bad, bad ∈ k4GadgetFamily →
        bad.Avoids (normalizedGraphModel k4FourOriginalEdge) :=
    (hensonForbiddenFamily_avoids_iff
      4 (by decide) k4FourOriginalEdge).2
      ⟨k4FourOriginalEdge_irreflexive,
       k4FourOriginalEdge_symmetric,
       k4FourOriginalEdge_cliqueFree⟩
  exact finiteNumericH_avoids_family
    (k4GadgetFamily)
    (normalizedGraphModel k4FourOriginalEdge)
    (by intro i; trivial)
    4 40 hBase

/-- The top original 38 is eligible to contribute its complete
upper Kpt crossing at cut 22. This uses the LITERAL numerical
generated E relation rather than a postulated free-cut formula. -/
theorem k4GadgetH_top_freeLevel_above22 :
    22 < k4GadgetH.freeLevel 38 := by
  have hE : k4GadgetH.E 22 38 = true := by
    change finiteNumericHE 4 40 22 38 = true
    apply (finiteNumericHE_true_iff 4 40 22 38).2
    refine ⟨by decide, ?_⟩
    have hGen : generatedE 4 3 4 22 :=
      generatedE_of_allowedPair 4 2 3 1 4
        (by decide) (by decide) (Or.inl (by decide))
    have hExact :=
      (exactHEBool_at_real_iff 4 3 4 22 (by decide)).2 hGen
    simpa [hPosition] using hExact
  exact (k4GadgetH.E_iff_freeLevel 22 38).1 hE

/-- This is the concrete Algorithm 5.4 result sought in the
circulation proof audit: **every actual full run** with the
specific genuine top Kpt original as a seed retains level 22.

No auxiliary source-set equality or hypothetical I3 injection is
assumed. The forcing is by one failed complete upper L-age test. -/
theorem k4Gadget_algorithmRun_selects_cut22
    (X : Set (AdmissibleKptNode
      (k4GadgetFamily)))
    (hSeed : k4GadgetH.kptOriginal
      (k4GadgetFamily) k4GadgetH_avoids
      (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈ X)
    (ell : Nat) (hEll : 22 < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (k4GadgetFamily))
      X ell) :
    22 ∈ R.I 22 := by
  exact algorithmRun_selects_actual_failed_single_upper_B3
    (k4GadgetFamily) k4GadgetH
    k4GadgetH_avoids
    (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size)
    22 (by decide) k4GadgetH_top_freeLevel_above22
    k4H_actual_cut22_singleUpper_B3_failure
    X hSeed ell hEll R

/-- Algorithm 5.4 scans downward, so a selected cut 22 remains in
the higher-level set at cut 10. The actual E-successor parameter of
the top original 38 at level 22 is the *full Kpt original of q2*.
Consequently q2 (free level 11) belongs to the real parameter-closed
source of the stage scanning cut 10. -/
theorem k4Gadget_algorithmRun_q2_in_cut10_closure
    (X : Set (AdmissibleKptNode
      (k4GadgetFamily)))
    (hSeed : k4GadgetH.kptOriginal
      (k4GadgetFamily) k4GadgetH_avoids
      (⟨38, by change 38 < 40; decide⟩ : Fin k4GadgetH.size) ∈ X)
    (ell : Nat) (hEll : 22 < ell)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree (k4GadgetFamily))
      X ell) :
    k4GadgetH.kptOriginal
      (k4GadgetFamily) k4GadgetH_avoids
      (⟨22, by change 22 < 40; decide⟩ : Fin k4GadgetH.size) ∈
      SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree (k4GadgetFamily))
        (R.I 11) X := by
  have hSelected22 : 22 ∈ R.I 22 :=
    k4Gadget_algorithmRun_selects_cut22 X hSeed ell hEll R
  have hFinal : 22 ∈ R.I 0 := by
    rw [R.I_eq_final_tail_of_run 22 (by omega)] at hSelected22
    exact hSelected22.1
  have hAt11 : 22 ∈ R.I 11 := by
    rw [R.I_eq_final_tail_of_run 11 (by omega)]
    exact ⟨hFinal, by omega⟩
  exact numericH_first_gadget_second_original_in_closure
    (k4GadgetFamily)
    (normalizedGraphModel k4FourOriginalEdge)
    k4GadgetH_avoids (R.I 11) X hSeed hAt11

end Kk
