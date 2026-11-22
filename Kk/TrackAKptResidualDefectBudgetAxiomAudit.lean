import Kk.TrackAKptResidualDefectBudget

/-!
Standalone strict exact-head audit. A theorem here is conditional
on two genuine Kpt AlgorithmRuns; none asserts that the refined
KK-free diary already bounds the residual profile defect set.
-/

#check @Kk.kpt_full_profiles_eq_of_not_mem_off_exception_defects
#print axioms Kk.kpt_full_profiles_eq_of_not_mem_off_exception_defects

#check @Kk.kpt_actual_runs_selected_disagreement_le_exception_plus_defects
#print axioms Kk.kpt_actual_runs_selected_disagreement_le_exception_plus_defects

#check @Kk.trackA_henson_physical_critical_cuts_card_le
#print axioms Kk.trackA_henson_physical_critical_cuts_card_le

#check @Kk.trackA_henson_kpt_selected_disagreement_le_sharp_plus_defects
#print axioms Kk.trackA_henson_kpt_selected_disagreement_le_sharp_plus_defects
