import Kk.OneGapFiniteCodingFront
import Kk.ResolvedFairSelectedFront
import Kk.ResolvedFairSelectedEnvelope

/-! Exact named audit of finite coding fronts and the assembled actual envelope. -/

-- OneGapFiniteCodingFront
#check @Kk.oneGapCodingFrontSet_mem
#print axioms Kk.oneGapCodingFrontSet_mem
#check @Kk.oneGapCodingFrontEntry_mem
#print axioms Kk.oneGapCodingFrontEntry_mem
#check @Kk.oneGapCodingFrontSelected_lt_size
#print axioms Kk.oneGapCodingFrontSelected_lt_size
#check @Kk.oneGapCodingFrontSelected_mem_pool
#print axioms Kk.oneGapCodingFrontSelected_mem_pool
#check @Kk.oneGapCodingFrontSelected_eligible
#print axioms Kk.oneGapCodingFrontSelected_eligible
#check @Kk.oneGapCodingFrontSelected_coded
#print axioms Kk.oneGapCodingFrontSelected_coded
#check @Kk.oneGapCodingFrontSelected_after_cut
#print axioms Kk.oneGapCodingFrontSelected_after_cut
#check @Kk.oneGapCodingFrontSelected_strictMono
#print axioms Kk.oneGapCodingFrontSelected_strictMono
#check @Kk.oneGapCodingFrontSelected_injective
#print axioms Kk.oneGapCodingFrontSelected_injective
#check @Kk.oneGapCodingFrontSelected_range
#print axioms Kk.oneGapCodingFrontSelected_range
#check @Kk.oneGapCodingFrontSize_le_size
#print axioms Kk.oneGapCodingFrontSize_le_size
#check @Kk.oneGapCodingFrontSize_zero_iff
#print axioms Kk.oneGapCodingFrontSize_zero_iff
#check @Kk.oneGapCodingFrontSet_antitone
#print axioms Kk.oneGapCodingFrontSet_antitone
#check @Kk.oneGapCodingFrontSize_antitone
#print axioms Kk.oneGapCodingFrontSize_antitone

-- ResolvedFairSelectedFront
#check @Kk.resolvedFairSelectedFront_lt_size
#print axioms Kk.resolvedFairSelectedFront_lt_size
#check @Kk.resolvedFairSelectedFront_strictMono
#print axioms Kk.resolvedFairSelectedFront_strictMono
#check @Kk.resolvedFairSelectedFront_range
#print axioms Kk.resolvedFairSelectedFront_range
#check @Kk.resolvedFairSelectedFront_positive
#print axioms Kk.resolvedFairSelectedFront_positive
#check @Kk.resolvedFairSelectedFront_other_zero
#print axioms Kk.resolvedFairSelectedFront_other_zero
#check @Kk.resolvedFairSelectedFront_range_iff_original
#print axioms Kk.resolvedFairSelectedFront_range_iff_original
#check @Kk.resolvedFairSelectedFront_original
#print axioms Kk.resolvedFairSelectedFront_original
#check @Kk.resolvedFairSelectedFrontSize_le_card
#print axioms Kk.resolvedFairSelectedFrontSize_le_card

-- ResolvedFairSelectedEnvelope
#check @Kk.resolvedFairRetainedCap_eligible_of_omitted
#print axioms Kk.resolvedFairRetainedCap_eligible_of_omitted
#check @Kk.resolvedFairRetainedFront_cap
#print axioms Kk.resolvedFairRetainedFront_cap
#check @Kk.resolvedFairRetainedFrontSize_pos_of_omitted
#print axioms Kk.resolvedFairRetainedFrontSize_pos_of_omitted
#check @Kk.resolvedFairRetainedFront_positive
#print axioms Kk.resolvedFairRetainedFront_positive
#check @Kk.resolvedFairRetainedFront_other_zero
#print axioms Kk.resolvedFairRetainedFront_other_zero
#check @Kk.resolvedFairEventGraph_avoids
#print axioms Kk.resolvedFairEventGraph_avoids
#check @Kk.resolvedFairRetained_envelope
#print axioms Kk.resolvedFairRetained_envelope
#check @Kk.resolvedFairFiniteSelection_envelope
#print axioms Kk.resolvedFairFiniteSelection_envelope
