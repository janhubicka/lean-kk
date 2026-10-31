import Kk.K4FullVsMarkedB3

/-!
# Failure of the full-to-selected upper-L-profile inclusion in the genuine K4 gadget

The selected x-only corrected B3 test is good at the first auxiliary
cut, while the full parameter-closed {q2,x} test is bad on the exact
same initial ordinary L-socle. We sharpen that fact to an explicit
failure of the "upper types included" hypothesis of the conditional
B3 reduct-profile transfer.

This rules out one particular shortcut to the canonical diary theorem:
the full permitted upper L-reduct family CANNOT be replaced by the
marked x-only family at cut 10, even though the lower L-socles agree.

It does not rule out a different globally resolved presentation.
-/

namespace Kk

open SuccessorTree.V10

/-- The full two-type upper L-profile of the actual numerical-H gadget
at cut 10 is NOT contained in the selected-only x-type profile.
This is the exact missing premise of correctedB3_of_Lprofile_dominance,
proved without assuming a global diary construction. -/
theorem k4Gadget_full_upper_not_subset_x_only :
    ¬ (∀ R,
      (R = (k4GadgetH.partialTypeAt 11 22).lReduct ∨
       R = (k4GadgetH.partialTypeAt 11 38).lReduct) →
      R = (k4GadgetH.partialTypeAt 11 38).lReduct) := by
  intro hSubset
  apply k4H_actual_cut10_twoUpper_B3_failure
  intro W hFinite hSame hUpperW hDelete bad hBad
  exact k4Gadget_cut10_selected_only_B3_good_on_full_socle
    W hFinite hSame
    (fun u hu hAbove => hSubset _ (hUpperW u hu hAbove))
    hDelete bad hBad

/-- The auxiliary complete upper L-reduct is genuinely distinct from
the selected complete upper L-reduct, even on their common lower socle. -/
theorem k4Gadget_q2_upper_L_reduct_ne_x :
    (k4GadgetH.partialTypeAt 11 22).lReduct ≠
      (k4GadgetH.partialTypeAt 11 38).lReduct := by
  intro hEqual
  apply k4Gadget_full_upper_not_subset_x_only
  intro R hR
  rcases hR with hQ | hX
  · exact hQ.trans hEqual
  · exact hX

end Kk
