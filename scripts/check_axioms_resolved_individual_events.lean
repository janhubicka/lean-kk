import Kk.ResolvedEventTrace
import Kk.ResolvedRoundEvents
import Kk.ResolvedFairEventOneGap

/-! Focused transitive-axiom audit of every public theorem in the three
individual-event extraction and canonical-source modules. -/

#check @Kk.ResolvedLiveStage.insertBlock_empty_oldAge
#print axioms Kk.ResolvedLiveStage.insertBlock_empty_oldAge
#check @Kk.resolvedCoverBlock_nonempty
#print axioms Kk.resolvedCoverBlock_nonempty
#check @Kk.ResolvedEventCertificate.block_pos
#print axioms Kk.ResolvedEventCertificate.block_pos
#check @Kk.ResolvedEventCertificate.block_nodup
#print axioms Kk.ResolvedEventCertificate.block_nodup
#check @Kk.ResolvedEventCertificate.block_fresh
#print axioms Kk.ResolvedEventCertificate.block_fresh
#check @Kk.ResolvedEventChain.old_mono
#print axioms Kk.ResolvedEventChain.old_mono
#check @Kk.ResolvedEventChain.append
#print axioms Kk.ResolvedEventChain.append
#check @Kk.ResolvedEventChain.transport
#print axioms Kk.ResolvedEventChain.transport
#check @Kk.ResolvedLiveCoverPath.old_mono
#print axioms Kk.ResolvedLiveCoverPath.old_mono
#check @Kk.ResolvedLiveCoverPath.preserves
#print axioms Kk.ResolvedLiveCoverPath.preserves
#check @Kk.ResolvedBareStage.refineBatch_exists_events
#print axioms Kk.ResolvedBareStage.refineBatch_exists_events
#check @Kk.ResolvedMarkerBatchStep.old_mono
#print axioms Kk.ResolvedMarkerBatchStep.old_mono
#check @Kk.ResolvedMarkerBatchStep.preserves
#print axioms Kk.ResolvedMarkerBatchStep.preserves
#check @Kk.ResolvedMarkerBatchStep.exists_events
#print axioms Kk.ResolvedMarkerBatchStep.exists_events
#check @Kk.ResolvedLiveCoverPath.exists_events
#print axioms Kk.ResolvedLiveCoverPath.exists_events
#check @Kk.ResolvedRoundResult.exists_events
#print axioms Kk.ResolvedRoundResult.exists_events
#check @Kk.resolvedFairEventOneGapPartial_avoids
#print axioms Kk.resolvedFairEventOneGapPartial_avoids
#check @Kk.resolvedFairEventOneGapOriginal_size
#print axioms Kk.resolvedFairEventOneGapOriginal_size
#check @Kk.resolvedFairEventOneGapOriginal_strictMono_size
#print axioms Kk.resolvedFairEventOneGapOriginal_strictMono_size
#check @Kk.resolvedFairEventOneGapOriginal_injective
#print axioms Kk.resolvedFairEventOneGapOriginal_injective
#check @Kk.resolvedFairEventOneGapOriginal_binary
#print axioms Kk.resolvedFairEventOneGapOriginal_binary
#check @Kk.resolvedFairEventOneGapOriginal_diagonal
#print axioms Kk.resolvedFairEventOneGapOriginal_diagonal
#check @Kk.resolvedFairEventOneGapOriginal_E
#print axioms Kk.resolvedFairEventOneGapOriginal_E
#check @Kk.resolvedInitialEventOneGapOriginal_binary
#print axioms Kk.resolvedInitialEventOneGapOriginal_binary
