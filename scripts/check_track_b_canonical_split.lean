import Kk.PhysicalFreeSplitRestriction
import Kk.ProtectedActivePivotRealization

/- The previous protected-pivot endpoints and the new arbitrary-map and
constructed-split endpoints are checked against their actual transitive axioms. -/

#check @Kk.protectedPivot_common_pool
#print axioms Kk.protectedPivot_common_pool
#check @Kk.protectedPivot_capacity
#print axioms Kk.protectedPivot_capacity
#check @Kk.protectedPivotRaw_eq_actual
#print axioms Kk.protectedPivotRaw_eq_actual
#check @Kk.activeGapPointedRaw_eq_actual
#print axioms Kk.activeGapPointedRaw_eq_actual
#check @Kk.henson_leftDense_realizes_activeGap_pointed
#print axioms Kk.henson_leftDense_realizes_activeGap_pointed
#check @Kk.protectedPivot_targetAge_le_canonical_iff_budgets
#print axioms Kk.protectedPivot_targetAge_le_canonical_iff_budgets
#check @Kk.integerCliquePushforward_feasible
#print axioms Kk.integerCliquePushforward_feasible
#check @Kk.integerClique_exists_lift_along_sortMap
#print axioms Kk.integerClique_exists_lift_along_sortMap
#check @Kk.integerGraphAgeCanonical_pullback_mono
#print axioms Kk.integerGraphAgeCanonical_pullback_mono
#check @Kk.isIntegerGraphAge_pullback
#print axioms Kk.isIntegerGraphAge_pullback
#check @Kk.finiteOldColumnCanonical_reindex
#print axioms Kk.finiteOldColumnCanonical_reindex
#check @Kk.finiteOldColumnCanonical_reindex_twice
#print axioms Kk.finiteOldColumnCanonical_reindex_twice
#check @Kk.finiteOldColumnCanonical_neutral_reindex
#print axioms Kk.finiteOldColumnCanonical_neutral_reindex
#check @Kk.protectedPivot_pulledBackAge_iff_budgets
#print axioms Kk.protectedPivot_pulledBackAge_iff_budgets
#check @Kk.freePointedContinuation_raw_eq
#print axioms Kk.freePointedContinuation_raw_eq
#check @Kk.freePointedContinuation_canonical_eq
#print axioms Kk.freePointedContinuation_canonical_eq
#check @Kk.freeSplit_canonical_eq
#print axioms Kk.freeSplit_canonical_eq
#check @Kk.henson_leftDense_constructs_freePointed_stage
#print axioms Kk.henson_leftDense_constructs_freePointed_stage
#check @Kk.henson_leftDense_constructs_freeSplit_stage
#print axioms Kk.henson_leftDense_constructs_freeSplit_stage
#check @Kk.integerGraphAgeCanonical_lowerAt_canonical
#print axioms Kk.integerGraphAgeCanonical_lowerAt_canonical
#check @Kk.freeSplit_raw_eq_lowerAt
#print axioms Kk.freeSplit_raw_eq_lowerAt
#check @Kk.freeSplit_canonical_eq_restriction
#print axioms Kk.freeSplit_canonical_eq_restriction
#check @Kk.henson_leftDense_constructs_exactFreeSplit_stage
#print axioms Kk.henson_leftDense_constructs_exactFreeSplit_stage
