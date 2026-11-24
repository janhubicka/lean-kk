# Independent review: omitted TOP-generation coherence

Date: 24 November 2026.

Reviewer: `common_source_audit`, independent of the proposal author
`generation_zero`.

Proposal reviewed:
`docs/top_generation_stage_coherence_english_20261124.md`.

Proposal SHA-256:
`9d1e0c2e948ec1140958fc7f9cbd7dc844d9bb984eca9229f8d5f449622d8e2d`.

## Verdict

Approved for implementation with the hypotheses and scope stated in the
proposal. The proof supplies the genuinely missing TOP branch of the
positive-generation structural argument. It neither assumes the full
structural conclusion nor tries to derive it from corrected B3 alone.
Compilation and axiom auditing remain subsequent validation steps.

I checked the proposal against the literal definitions and statements in
the pinned successor dependency and the existing local modules:

- `SuccessorTree/V10/HNumericBinary.lean`: `HNumericCrossing`,
  `hNumericBinary_true_iff`, and `hNumericBinary_real_forward_iff`;
- `SuccessorTree/V10/HExactE.lean`: bounded real-address injectivity;
- `Kk/PhysicalLowerRealCutNeighbour.lean`: the existing directed decoder,
  whose hypothesis is strictly `g < k`;
- `Kk/TrackDPlannedStageRoles.lean`: the literal current-stage original
  pool and bounded omitted-base positive-neighbour classification;
- `Kk/PositiveGenerationStageCoherence.lean` and
  `Kk/EqualCutFullType.lean`: the old generation-zero coordinate and the
  complete next-column argument;
- `Kk/StageCoherenceStructural.lean`: full closure representation and
  the generic no-I1/no-I2 lift;
- `Kk/ActualRunStructuralOrLowerReal.lean`: the actual-run classifier
  for selected positive cuts after both structural exclusions.

## Directed TOP decoder

The new decoder cannot be obtained by instantiating the existing lower
decoder with `g = k`. The proposal correctly unfolds the exact crossing
predicate instead. In its forward orientation, bounded injectivity
identifies the cut's decoded generation with `k`. The generator gate
then forces the other generation to equal `k`, since that generation is
bounded by `k`. The directed ordinary bit remains precisely `B(b,j)`.

In the reverse orientation, numerical block order makes the purported
later neighbour strictly earlier than the cut. This contradicts the
explicit strict-order hypothesis. The argument requires no ordinary
symmetry and remains valid at `k = 0`.

For a finite eligible original, strict order is derived from
`cut + 1 <= freeLevel(v) <= v`. Thus eligibility supplies the needed
chronology for every actual name; the decoder does not silently impose
a selected-tuple or real-name restriction.

## Whole-column equality and complete types

At `k > 0`, write `c = p(b,k)` and `q = p(b,0)`. Then `q < c`, and
eligibility at `c` implies eligibility at `q`.

The forward positive-bit implication follows from the TOP decoder and
the open generation-zero-to-TOP gate. The converse requires more than
the existence of that gate: the generation-zero decoder initially only
gives `0 < m <= k`. The stated bounded whole-stage role theorem is what
forces this `m` to be `k`. Its premises are all retained: actual
`J subset Plan`, bounded dummy-root roles, bounded positive-free-level
Plan roles, the chronological resolved-Q axioms, and the tested base's
omitted role. This is the decisive noncircular use of the current-stage
geometry.

Both implications are proved, so equality includes false bits. The
universal quantifier still ranges over all eligible current-stage
originals, including the root names and retained auxiliary names.
A positive relation bit supplies the bounded real presentation only
inside the positive cases.

Complete old-type equality exposes the ordinary bit at the strictly old
coordinate `q`. Equality of cut bits follows from the two column-copy
identities. The existing `full_equal_ordinary_cut_column_determines_next_type`
then uses ordinary symmetry and eligibility to handle both ordinary
directions, forward and reverse auxiliary E, and the remaining common
new-coordinate atoms. The claim is equality of complete L+/E types,
including negative information; it is not merely equality of graph ages.

The proposed split `0 < g < k` or `g = k` yields precisely the unified
range `0 < g <= k`. The old-coordinate proof must not be extended to
generation zero or to `k = 0`.

## Full closure and actual AlgorithmRun consequences

The generic structural lift accepts arbitrary seed families represented
by the actual root originals. It proves both full I1 and full I2
exclusions from whole-stage coherence, positive even-real cut, and seed
absence. Its proof includes generated closure parameters, meets,
endpoints, and self-meets. Consequently it remains applicable to the
enlarged family of planned cap ancestors; no substitution of the smaller
literal TOP-prefix family is justified or needed.

Seed absence is a real premise of the generic theorem. For the explicit
planned-prefix construction it follows from `c` lying outside the Plan.
The actual descending-stage inclusion is also a real premise; the
proposed TOP lemma is a local induction step, not a proof that the
final level set already equals the Plan.

After structural exclusion, the cited Henson actual-run theorem says
that any selected positive cut below the top and inside the finite
carrier has a bounded presentation with generation strictly below `k`.
Comparing this presentation with `p(b,k)` by bounded injectivity is
impossible. This proves actual TOP nonselection using the established
full-source corrected-B3 classifier, without introducing a marked-B3
assumption or treating TOP B3 as structural coherence.

The optional noninterestingness adapter is valid at the literal
pre-cut stage: `interesting_step` inserts `c` into `Run.I(c)`, and the
standard final-tail identity transfers that membership to `Run.I(0)`.
The hypothesis `c < top` must remain available when invoking the step.

## Scope of the approval

This approval closes the mathematical TOP case under the explicit
bounded role, source-representation, finite-bound, seed-absence, and
descending-stage hypotheses. It does not verify an infinite resolved-Q
construction, record-dependent marked age invariants at lower real
cuts, or the complete characterisation theorem. Those separate
obligations must remain visible in the eventual theorem statements
and manuscript validation status.
