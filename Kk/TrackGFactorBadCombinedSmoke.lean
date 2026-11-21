import Kk.TrackGIntrinsicExactFactorBad
import Kk.TrackGExactFactorBadWitness

/-!
# Track G: combined-import coherence smoke test

The earlier verified TrackGIntrinsicExactFactorBad is the canonical
implementation of physically intrinsic exact factor-Bad support,
index independence and finite-H+ target-index reduction.

The later verified TrackGExactFactorBadWitness supplies genuinely
new terminal/I2-meet/factor-mismatch witnesses and old-pair novelty.
The accidentally duplicated PR #426 module was retired.

This module deliberately imports BOTH canonical index independence
and the novel witness theorem in a single Lean environment.
It contains no new mathematical axiom or unsupported BRD claim.
-/

#check @Kk.KptPhysicalOldFactorCompatibleAt
#check @Kk.kptIndexedOldFactorCompatibleAt_iff_physical
#check @Kk.kptExactOldFactorBadCuts_index_independent
#check @Kk.finiteNumericH_construct_target_exact_factor_Bad_iff_transport
#check @Kk.kpt_exact_factor_bad_has_terminal_meet_or_mismatch
#check @Kk.kpt_old_boring_factor_mismatch_has_no_old_full_pair
