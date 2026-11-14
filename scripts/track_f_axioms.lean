import Kk.DiaryCoverColumn
import Kk.TrackFLabelledFibre
import Kk.TrackFCodingColumn
import Kk.TrackFRawCoverColumn
import Kk.TrackFCoverEssentialSupport
import Kk.TrackFCoverOneStep
import Kk.TrackFCoverSupportValues
import Kk.TrackFLiteralWordColumns

-- Track F's *local* exact-head certificate; no changes to G's global registry.
#print axioms Kk.diaryCoverColumnRaw_le_upper
#print axioms Kk.diaryCoverColumnCanonical_exact
#print axioms Kk.diaryCoverColumn_feasible_iff_lower
#print axioms Kk.trackF_card_labelled_diaries

#print axioms Kk.trackFCodingRaw_le_original
#print axioms Kk.trackFCodingColumn_canonical_eq
#print axioms Kk.trackFCodingColumn_feasible_iff

#print axioms Kk.trackFCodingRaw_witness_iff
#print axioms Kk.trackFCanonical_eq_of_feasible_iff
#print axioms Kk.trackFCanonical_add_cap_congr
#print axioms Kk.trackFRawCoverColumn_exact
#print axioms Kk.trackFRawCoverColumn_feasible_iff_lower

#print axioms Kk.trackFCover_exists_minimal_changed
#print axioms Kk.trackFCover_unique_minimal_changed
#print axioms Kk.trackF_integerWitness_drop_one
#print axioms Kk.trackFCover_drop_one_at_changed
#print axioms Kk.trackFCover_drop_at_most_one
#print axioms Kk.trackFCover_single_support_canonical
#print axioms Kk.trackFCover_changed_values_of_containment
#print axioms Kk.trackFCover_essential_contained_in_changed
#print axioms Kk.trackFCover_all_changed_upper_eq_essential
#print axioms Kk.trackFColumnRepresentative_mem
#print axioms Kk.trackFNewColumnCommon
#print axioms Kk.trackFWordRaw_append
#print axioms Kk.trackFWordRaw_append_as_coding_cap
#print axioms Kk.trackFWord_cover_symbol_valid
#print axioms Kk.trackFWordRaw_age_cover_exact
#print axioms Kk.trackFWordRaw_coding_preserves_age
