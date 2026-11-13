import Kk.DiaryCoverColumn
import Kk.TrackFLabelledFibre
import Kk.TrackFCodingColumn
import Kk.TrackFRawCoverColumn
import Kk.TrackFCoverOneStep

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

#print axioms Kk.trackF_integerWitness_drop_one
#print axioms Kk.trackFCover_drop_one_at_changed
#print axioms Kk.trackFCover_drop_at_most_one
