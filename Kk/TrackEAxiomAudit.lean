import Kk.FullEventIndexedOrbitBridge

/-!
Standalone Track-E exact-declaration audit. This file is intentionally
not added to the shared Kk.lean or scripts/check_axioms.lean until
integration owner Track G reviews the exact-head result.
-/

#check @Kk.fullLabelledSourceRecord_ext
#print axioms Kk.fullLabelledSourceRecord_ext

#check @Kk.full_source_records_eq_of_inverse_comparison
#print axioms Kk.full_source_records_eq_of_inverse_comparison

#check @Kk.common_labelled_orbit_of_full_record_eq
#print axioms Kk.common_labelled_orbit_of_full_record_eq

#check @Kk.full_source_coherence_implies_diary_colour_bound
#print axioms Kk.full_source_coherence_implies_diary_colour_bound

#check @Kk.pairwise_full_source_comparison_implies_diary_colour_bound
#print axioms Kk.pairwise_full_source_comparison_implies_diary_colour_bound

#check @Kk.fullEventIndexedSourceRecord_ext
#print axioms Kk.fullEventIndexedSourceRecord_ext
#check @Kk.KptClosureRecipe.evaluate_congr
#print axioms Kk.KptClosureRecipe.evaluate_congr
#check @Kk.KptClosureRecipe.wellFormed_congr
#print axioms Kk.KptClosureRecipe.wellFormed_congr
#check @Kk.full_event_source_eq_of_inverse_sets_and_recipes
#print axioms Kk.full_event_source_eq_of_inverse_sets_and_recipes
#check @Kk.full_event_source_coherence_implies_diary_colour_bound
#print axioms Kk.full_event_source_coherence_implies_diary_colour_bound
#check @Kk.event_kind_does_not_determine_inputs
#print axioms Kk.event_kind_does_not_determine_inputs
#check @Kk.assigned_upper_type_requires_event_indexing
#print axioms Kk.assigned_upper_type_requires_event_indexing

#check @Kk.full_event_source_eq_of_local_reconstruction
#print axioms Kk.full_event_source_eq_of_local_reconstruction
#check @Kk.full_event_source_common_selected_and_parameter_targets
#print axioms Kk.full_event_source_common_selected_and_parameter_targets
