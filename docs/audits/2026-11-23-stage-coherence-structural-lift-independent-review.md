# Independent review: lifting whole-stage coherence to structural exclusion

Reviewed before Lean implementation on 23 November 2026 by the manuscript
review agent, independently of the author of the English proof.

Reviewed source:
`docs/stage_coherence_structural_lift_english_20261123.md`

SHA256:
`86b4c78887ba6fc0e103e3643af9cbe0fc005012b68968522c2e4373e4010c43`

## Verdict

Approved for implementation. This records independent mathematical/source
review; kernel validation of the new implementation remains pending.

## Checked interfaces and implications

1. The meet proof in `TrackDZeroMeetObstruction.lean` uses zero ordinary bits
   and symmetry only in its complete next-type uniqueness call. Replacing
   that call by the displayed old-to-next implication preserves the exact
   proof. Both genuine eligibility inequalities and same-component originals
   remain explicit.
2. `finiteNumericH_even_real_level_nonseed_is_original_meet` covers every
   nonseed closure terminal, including generated parameter and meet nodes.
   Its witnesses belong to the whole `ambientStagePool`, not a selected or
   strictly crossing subpool.
3. The meet level gives `c ≤ freeLevel` for each witness. Positivity of c
   makes both free levels positive, and the exact numerical-H parity theorem
   excludes equality with this even position. Thus `c+1 ≤ freeLevel` is
   derived legitimately. No inference from address order substitutes for it.
4. The strict-fork proof in `TrackDZeroStarFullI2.lean` obtains both complete
   old and next records through each same actual original representative.
   Whole-name coherence can replace its zero-column uniqueness call without
   inventing source representatives or identifying different ambient socles.
5. `kpt_no_I1_I2_iff_complete_full_fork` requires no-I1. The proposed lift
   retains it, so self-meets and terminals at c are not silently discarded.
6. The definitions of `ambientStagePool` and `hStageOriginals` give the same
   membership condition after Finset/Set coercion. `hOriginalName` is the
   value of `Stage.equivFin.symm`; therefore the proposed `equivFin` naming
   preserves actual addresses, with no injectivity-of-types assumption.
7. `finiteNumericH_stage_closure_represented_by_stage_originals` holds for
   arbitrary I and has no no-I2 premise. Consequently the source coverage
   needed for the structural proof is obtained before structural exclusion.
8. The concrete endpoint uses `J = Run.I (c+1)` and the previously reviewed
   bounded positive-generation coherence theorem. The strict condition
   `0 < g` provides a positive real cut and is not extended to generation
   zero. No final-pool equality, block interval or selected independence
   premise is needed for this local implication.
9. `numericHTopGenerationSeeds_noPositiveLowerReal` and
   `numericHTopGenerationSeeds_subset_rootPool` supply precisely the seed
   absence and root representation needed for the literal cap/TOP-prefix
   source. Top-seed existence and `c < top` are retained separately for the
   optional actual-run nonselection composition.
10. The optional composition matches the planned-stage marked-B3 endpoint:
    its no-I1/no-I2 arguments are supplied by the new structural bundle, and
    the actual chosen Marked corrected-B3 premise is still supplied by the
    caller. Structural coherence does not prove the B3 age verdict.

## Boundaries

Approval covers the conditional local statements as written. It does not
construct the actual Q/Plan assignment or descending inclusion, settle
generation-zero structural coherence, prove the chosen corrected-B3 tests,
or identify a common labelled source orbit. The bounded root/Plan repair must
be used throughout; the old unbounded address hypotheses cannot be reimported
as application premises.
