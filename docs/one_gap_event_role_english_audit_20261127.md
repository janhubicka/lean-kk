# Roles from a chronological stream of positive event blocks

## English proof before Lean implementation

Let `size : Nat -> Nat` give the number of vertices in each chronological
event, with `0 < size n` for every event index `n`. The already proved
`oneGapBatchIndex size hPositive i` identifies the unique event containing
the unpadded vertex position `i`. Its fibre is exactly the interval between
the corresponding cumulative boundaries. Thus each event index identifies
one occurrence in the global chronological stream.

Supply two Boolean functions on event indices: `isCode` and `keep`.
Every vertex of one event uses the same coding flag and the same retention
flag. At the meaningful padded coordinate `oneGapAddress i = 2*i+2`, define
the role to be `coded (keep n)` if event `n` is coding, and
`auxiliary n (keep n)` otherwise, where `n` is the batch index of `i`.
The anchor `0` and all odd gap coordinates have role `dummy`.

An auxiliary block identifier is therefore the global event index itself.
It is not the support of an age change, an original vertex name, or a
round-local index. Distinct occurrences receive distinct identifiers even
when they have identical support or otherwise identical event data.

## Exact roles and uniform flags

At a meaningful coordinate, the definition directly gives its event's
role. Applying the batch-index interval theorem at a tagged position in
event `n` identifies the index with `n`, so every position of that event
has the asserted role and flag. A coordinate has auxiliary role
`auxiliary n b` exactly when it is meaningful, its batch index is `n`,
`isCode n` is false, and `keep n = b`.

Consequently, if two coordinates have auxiliary roles with the same block
identifier, both retention flags equal the single value `keep n`; their
flags are equal. For a meaningful coordinate, being a retained base is
equivalent to its event's keep flag being true, whether the event is
coding or auxiliary. Dummies are retained by the existing
`ResolvedQRetainedBase` definition.

## Convexity after ignoring dummy coordinates

Suppose `a < b < c` and both endpoints have role `auxiliary n true`.
The exact auxiliary-role characterization identifies both endpoints as
meaningful coordinates in event `n`, whose keep flag is true and coding
flag is false.

If `b` is not meaningful, its role is dummy and the first alternative of
`OneGapBlockConvex` holds. Otherwise the inverse one-gap positions obey
`oneGapIndex a <= oneGapIndex b <= oneGapIndex c`. The existing convexity
theorem for batch-location fibres places the middle position in event
`n`. The event's unchanged flags then give role `auxiliary n true` at `b`.
This proves exactly the dummy-aware `OneGapBlockConvex` used by the full
retained-pool old-column argument.

This proof also covers single-vertex events. In that case two distinct
meaningful endpoint positions in the same event cannot occur. No
assumption that auxiliary events have at least two members is needed.

## Scope and integration

The construction is generic in the positive sizes and two event flags.
It has no graph argument and proves no edge or old-column-zero claim.
In particular, it does not prove that a code event has one vertex; that
fact must come from the actual event certificate when this role is
instantiated. Nor does it identify the keep flags with any selected
support rule or establish projected diary legality.

An actual event stream supplies positive sizes, the coding test, and one
chosen keep flag per global event occurrence. The module then discharges
the uniform auxiliary-block flag and chronological block-convexity
premises without any additional geometric assumption. Actual birth-edge
geometry and its preservation in the limit remain separate inputs to
the later graph application.

Independent English-proof review: **PASS** before implementation. The
review checked uniqueness of global event indices, constructor equality
for uniform flags, weak inequalities of inverse one-gap coordinates,
and the dummy alternative in the exact convexity definition. It also
checked that retaining every dummy as a base role does not assert that
every dummy level belongs to a later finite paired retained-level set.
An independent review of the completed source also passed, checking the
exact auxiliary-role equivalence and the two final flag/convexity proofs.

Local Lean module validation: **PASS** on 27 November 2026. The direct
`lake env lean` check of the final source exited successfully, wrote the
module object, and left an empty diagnostic log at
`proof-audit/one-gap-event-role-local.log`. The full root build and central
axiom audit remain **PENDING** integration gates. The focused
`scripts/check_axioms_resolved_fair_event_geometry.lean` names all eleven
Role endpoints and all sixteen actual-Geometry endpoints explicitly.

## Final integration checkpoint — 27 November 2026

The later integration gate supersedes the pending validation statuses at
the component checkpoints above. The normal new-module targets passed
(3,614 jobs), the default project build passed (4,123 jobs), all five focused
Lean audits and strict parsers passed, and the central audit accepted all
1,394 exact names, including every one of the 111 new endpoints. Only
`propext`, `Classical.choice` and `Quot.sound` appear; fourteen central names
are axiom-free. Parser tests, source/import coverage and the diff check pass.
See the [completed integration report](resolved_event_completion_20261127.md)
and [source-hash/axiom evidence](audits/2026-11-27-resolved-events-completion.json)
for exact scope and the four remaining application obligations.
