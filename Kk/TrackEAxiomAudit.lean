import Kk.FullLabelledOrbitBridge

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
