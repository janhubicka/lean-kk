import Kk.OneGapEventScheduleOrder
import Kk.ResolvedEventChainOrder
import Kk.ResolvedFairEventSchedule

/-! Exact named audit of the ordered actual-event schedule and prefix theorems. -/

-- OneGapEventScheduleOrder
#check @Kk.oneGapBatchIndex_mono
#print axioms Kk.oneGapBatchIndex_mono
#check @Kk.oneGapBatchPosition_lt_iff
#print axioms Kk.oneGapBatchPosition_lt_iff
#check @Kk.oneGapChronologicalVertex_prefix_at_entry
#print axioms Kk.oneGapChronologicalVertex_prefix_at_entry

-- ResolvedEventChainOrder
#check @Kk.ResolvedEventChain.event_certificate
#print axioms Kk.ResolvedEventChain.event_certificate
#check @Kk.ResolvedEventChain.event_postOld_subset
#print axioms Kk.ResolvedEventChain.event_postOld_subset
#check @Kk.ResolvedEventChain.event_agreement
#print axioms Kk.ResolvedEventChain.event_agreement
#check @Kk.ResolvedEventChain.vertices_mem
#print axioms Kk.ResolvedEventChain.vertices_mem
#check @Kk.ResolvedEventChain.vertices_nodup
#print axioms Kk.ResolvedEventChain.vertices_nodup
#check @Kk.ResolvedEventChain.preOld_iff
#print axioms Kk.ResolvedEventChain.preOld_iff
#check @Kk.ResolvedEventChain.blocks_disjoint
#print axioms Kk.ResolvedEventChain.blocks_disjoint

-- ResolvedFairEventSchedule
#check @Kk.resolvedFairRound_exists_event_list
#print axioms Kk.resolvedFairRound_exists_event_list
#check @Kk.resolvedFairRoundEvents_chain
#print axioms Kk.resolvedFairRoundEvents_chain
#check @Kk.resolvedFairRoundEvents_last
#print axioms Kk.resolvedFairRoundEvents_last
#check @Kk.resolvedFairRoundEvents_positive
#print axioms Kk.resolvedFairRoundEvents_positive
#check @Kk.resolvedFairEvent_at_position
#print axioms Kk.resolvedFairEvent_at_position
#check @Kk.resolvedFairEvent_certificate
#print axioms Kk.resolvedFairEvent_certificate
#check @Kk.resolvedFairEvent_agreement
#print axioms Kk.resolvedFairEvent_agreement
#check @Kk.resolvedFairEvent_prior_blocks
#print axioms Kk.resolvedFairEvent_prior_blocks
#check @Kk.resolvedFairEvent_preOld_at_position
#print axioms Kk.resolvedFairEvent_preOld_at_position
#check @Kk.resolvedFairEvent_preOld_iff
#print axioms Kk.resolvedFairEvent_preOld_iff
#check @Kk.resolvedFairEventBlock_positive
#print axioms Kk.resolvedFairEventBlock_positive
#check @Kk.resolvedFairEventBlock_nodup
#print axioms Kk.resolvedFairEventBlock_nodup
#check @Kk.resolvedFairEventBlock_disjoint
#print axioms Kk.resolvedFairEventBlock_disjoint
#check @Kk.resolvedFairEventVertex_injective
#print axioms Kk.resolvedFairEventVertex_injective
#check @Kk.resolvedFairEventVertex_prefix
#print axioms Kk.resolvedFairEventVertex_prefix
#check @Kk.resolvedFairEventVertex_prefix_inside
#print axioms Kk.resolvedFairEventVertex_prefix_inside
#check @Kk.resolvedFairEventVertex_range
#print axioms Kk.resolvedFairEventVertex_range
#check @Kk.resolvedFairCodingEvent_spec
#print axioms Kk.resolvedFairCodingEvent_spec
#check @Kk.resolvedFairCodingEvent_strictMono
#print axioms Kk.resolvedFairCodingEvent_strictMono
#check @Kk.resolvedFairEventVertex_coded
#print axioms Kk.resolvedFairEventVertex_coded
#check @Kk.resolvedFairEventCodePosition_strictMono
#print axioms Kk.resolvedFairEventCodePosition_strictMono
#check @Kk.resolvedFairEventEdge_sym
#print axioms Kk.resolvedFairEventEdge_sym
#check @Kk.resolvedFairEventEdge_loops
#print axioms Kk.resolvedFairEventEdge_loops
#check @Kk.resolvedFairEventEdge_free
#print axioms Kk.resolvedFairEventEdge_free
#check @Kk.resolvedFairEventEdge_originals
#print axioms Kk.resolvedFairEventEdge_originals
#check @Kk.resolvedInitialEventGraph_originals
#print axioms Kk.resolvedInitialEventGraph_originals
