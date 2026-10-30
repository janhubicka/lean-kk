import Kk.K4Cut10SelectedOnlyB3
import Kk.K4NumericalHCut10Transfer
import Kk.K4ActualAlgorithmRunCut10
import Mathlib.Tactic

/-!
# Literal numerical H counterexample to auxiliary B3 shadow projection

The exact K4 first-clique-gadget cut 10 has one marked active
future type x=38 and a parameter-closed auxiliary future type q2=22.

The earlier-clone argument proves the corrected B3 test for ONLY x
is good (the old original p=8 is a redundant clone of cut10 for x).
The actual finite 14-vertex mixed continuation proves that if q2 is
also admitted, the same finite L-socle admits a *new* K4 at cut10.

This module puts both statements over the EXACT SAME prescribed
ordinary L-socle, not merely isomorphic or different chosen bases.
The comparison is in the verified normalized complete directed
L-test and is independent of any finite graph-age enumeration.

The separate actual AlgorithmRun theorem confirms that both q1=10
and q2=22 are genuinely selected when x=38 is seeded. Thus
projecting the full parameter-closed B3 test to the selected
x-only upper type IS NOT VALID in the literal numerical H model.

Neither statement alone asserts that this numerical H is the
specific globally resolved labelled diary used for the paper's
exact-degree formula. Canonical diary identification and common
labelled source equivariance remain open obligations.
-/

namespace Kk

open SuccessorTree.V10

/-- Complete ordinary L-socles of any two original types extracted
from the SAME finite ambient H agree through cut10 (carrier and all
directed, singleton and diagonal atoms), even when their E and
upper L-incidences differ. -/
theorem k4Gadget_q2_and_x_have_same_old_L_socle :
    SameInitialL
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 38))
      10 := by
  have hQ :
      SameInitialL
        (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
        k4GadgetH.L 10 :=
    ambient_partialType_prescribedSocle k4GadgetH 10 22 (by decide)
  have hX :
      SameInitialL
        (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 38))
        k4GadgetH.L 10 :=
    ambient_partialType_prescribedSocle k4GadgetH 10 38 (by decide)
  have hReverse : SameInitialL k4GadgetH.L
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 38))
      10 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      exact (hX.1 x hx).symm
    · intro x y hx hy t
      exact (hX.2.1 x y hx hy t).symm
    · intro x hx t
      exact (hX.2.2.1 x hx t).symm
    · intro x hx t
      exact (hX.2.2.2 x hx t).symm
  exact hQ.trans hReverse

/-- Over the VERY SAME lower L-socle as the full auxiliary test,
a finite continuation with only the x=38 complete upper L-type
cannot create any new forbidden K4, loop or asymmetric pair at
cut 10. The old original p=8 blocks the would-be new clique. -/
theorem k4Gadget_cut10_selected_only_B3_good_on_full_socle :
    CommonSocleAgeTest k4GadgetFamily
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
      10
      (fun R => R = (k4GadgetH.partialTypeAt 11 38).lReduct) := by
  intro W hFinite hSame hUpper hDelete bad hBad
  exact k4Gadget_cut10_x_only_B3_good
    W hFinite
    (hSame.trans k4Gadget_q2_and_x_have_same_old_L_socle)
    hUpper hDelete bad hBad

/-- The ACTUAL numerical-H auxiliary shadow counterexample:
corrected B3 passes for the selected x-only complete upper type
but fails for the two-type family {x,q2} over the SAME L-socle.

This is a definite FALSE implication, not an unverified
geometrical guess about source membership. -/
theorem k4Gadget_cut10_full_B3_does_not_project_to_selected :
    CommonSocleAgeTest k4GadgetFamily
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
      10
      (fun R => R = (k4GadgetH.partialTypeAt 11 38).lReduct) ∧
    ¬ CommonSocleAgeTest k4GadgetFamily
      (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
      10
      (fun R => R = (k4GadgetH.partialTypeAt 11 22).lReduct ∨
        R = (k4GadgetH.partialTypeAt 11 38).lReduct) :=
  ⟨k4Gadget_cut10_selected_only_B3_good_on_full_socle,
    k4H_actual_cut10_twoUpper_B3_failure⟩

/-- Contrapositive phrasing: the proposed inference from an
unchanged selected x-only B3 test to full two-type admissibility
is false in the literal numerical-H instance. -/
theorem k4Gadget_cut10_selected_only_cannot_certify_full_B3 :
    ¬ (CommonSocleAgeTest k4GadgetFamily
        (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
        10
        (fun R => R = (k4GadgetH.partialTypeAt 11 38).lReduct) →
       CommonSocleAgeTest k4GadgetFamily
        (prescribedOrdinarySocle (k4GadgetH.partialTypeAt 11 22))
        10
        (fun R => R = (k4GadgetH.partialTypeAt 11 22).lReduct ∨
          R = (k4GadgetH.partialTypeAt 11 38).lReduct)) := by
  intro h
  exact k4Gadget_cut10_full_B3_does_not_project_to_selected.2
    (h k4Gadget_cut10_full_B3_does_not_project_to_selected.1)

end Kk
