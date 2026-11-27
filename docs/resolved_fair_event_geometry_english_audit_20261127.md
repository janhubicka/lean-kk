# Ordinary geometry of the actual fair event enumeration

## English proof before Lean implementation

Start with an actual initial bare stage `s0` for the K4 construction and
assume its old pool is empty. Use the newly constructed countable event
schedule, its positive event blocks, and its vertex enumeration. Every
event retains its actual certificate and agrees with the single fair-limit
graph on its post-old pool and the original live set of its round.

The graph `resolvedFairEventEdge s0` reads the actual fair-limit edge table
along the chronological vertex enumeration. Its one-gap padding is
`oneGapEdge (resolvedFairEventEdge s0)`.

## Earlier events and auxiliary birth edges

Let event occurrence `a` precede event occurrence `b`, and let `p` and `q`
belong to their respective actual blocks. The exact pre-old prefix theorem
puts `p` in event `b`'s actual pre-old pool. If event `b` is not coding,
the proved birth-geometry theorem makes both bits between `p` and `q`
false in its stored actual edge table.

Both endpoints lie in event `b`'s post-old pool: `p` was already old, and
`q` belongs to the new block. Localized agreement with the fair-limit graph
therefore transfers both false bits to that graph. No equality on unused
names is needed, and no zero-edge premise is supplied.

Every chronological vertex position belongs to its uniquely indexed
event block. Applying the preceding argument gives zero edges whenever
the first vertex belongs to an earlier event and the second belongs to
an auxiliary event. For vertices of distinct auxiliary occurrences,
compare their global event indices and apply the same argument with the
later event. The two directions of the birth theorem cover either order.

## Actual padded roles

Supply one Boolean keep flag per global event occurrence. Instantiate
`oneGapEventRole` with the lengths of the actual event blocks, coding flag
`event.kind = code`, and that keep function. Thus auxiliary block IDs are
global chronological occurrence indices; repeated essential supports
never merge separate blocks.

At a meaningful coordinate, the exact auxiliary-role characterization
identifies its event index, asserts that its event is not coding, and
identifies its keep flag. The coding-role characterization instead
asserts that the corresponding event is coding. Every nonmeaningful
coordinate is a dummy.

An earlier meaningful coding coordinate has no edge to a later auxiliary
coordinate. Indeed their inverse one-gap positions preserve order, and
the event-index function is monotone. The two event indices cannot be
equal because their kinds differ. Therefore the auxiliary coordinate
belongs to a strictly later event, and the established chronological
zero-edge theorem applies.

Coordinates in two distinct auxiliary blocks have no edge by their
distinct global event indices and the preceding auxiliary-event argument.
A dummy coordinate has a zero ordinary row by the definition of one-gap
padding. Uniform auxiliary flags and convexity modulo dummy coordinates
come from `OneGapEventRole` without any further assumptions.

## Later retained auxiliary old columns

These are precisely the graph and role premises of
`oneGap_later_retained_aux_old_zero`. Apply that theorem to the actual
padded event graph and the constructed roles. If `i < cut < j`, the cut's
role is omitted, and `j` belongs to a kept auxiliary block, then the bit
from `i` to `j` is false.

The same-block case uses actual chronological convexity: a kept auxiliary
block cannot have meaningful vertices on both sides of an omitted role.
The other cases use the derived earlier-code/later-auxiliary nonedges,
different-block nonedges, or the dummy zero row. Since every dummy is a
retained base role, an omitted role is necessarily meaningful. This does
not assert that every dummy level lies in an eventual finite retained
level set.

## Two retained-role consequences

First, suppose the tested role is omitted, a later vertex has a retained
base role, and its ordinary cut bit is positive. The existing retained-role
classification theorem applies with the graph premises just derived.
For its omitted-role classification, a coded role is already an allowed
case, while an auxiliary role must have false keep flag: a true flag would
contradict omission. Dummy rows are zero. The padded graph is symmetric
because the actual event graph is symmetric and the real-coordinate test
is symmetric in the two endpoints. The classification theorem therefore
forces the later vertex's role to be `coded true`.

Second, suppose a later vertex has a retained base role but its role is
not `coded true`. The definition of retained base leaves exactly the
dummy and kept-auxiliary cases. In the dummy case its ordinary column is
zero by the one-gap definition. In the auxiliary case the preceding
old-column theorem applies. Thus its entire ordinary column before an
omitted cut is zero.

These conclusions concern the role `coded true`, meaning a coding event
whose chosen keep flag is true. They do not identify such vertices with
the entries of any finite selected terminal list. That identification
remains an explicit task for the later parser and retained-pool assembly.

## Scope and remaining obligations

The graph conclusions concern the actual K4 fair construction and its new
individual-event enumeration. They require an empty initial old pool for
the exact prefix bridge. All ordinary zero-edge conclusions are derived
from actual insertion certificates and their preservation; none is an
additional construction assumption.

The keep function remains arbitrary but is constant on each event
occurrence. This module does not derive the keep rule from a projected
diary, prove selected-age neutrality or no-splitting at omitted real
cuts, construct a common inverse source, or assert a G+ comparison. The
actual event schedule and the birth-geometry theorem supply exactly the
chronological graph premises used here.

Independent English review: **PASS** before implementation. The review
checked exact pre-old membership, the localized agreement domain, both
orders of distinct auxiliary occurrences, and the kind inequality needed
for an earlier code and later auxiliary vertex. It also checked the
distinction between an omitted base role and an omitted finite level.
An independent review of all fourteen completed theorem proofs also
passed, including both localized agreement domains and the exact argument
order of the final full-pool theorem application.
The two subsequent retained-role corollaries received an independent
English-proof review before implementation as well. That review checked
the exact existing classification theorem, the absence of any independence
premise, and the distinction between a kept coding role and finite selected
list membership. Their completed-source review also passed, bringing all
sixteen theorem proofs under independent source review.

Direct local Lean module validation: **PASS** on 27 November 2026 for
the final source containing all sixteen endpoints. The centrally run
serial check exited successfully; its diagnostic log is
`proof-audit/ResolvedFairEventGeometry-local.log`.

Normal Lake target/full-root validation and the named axiom audit remain
**PENDING**. The focused Role-plus-Geometry audit script explicitly checks
and prints axioms for all twenty-seven theorem endpoints:
`scripts/check_axioms_resolved_fair_event_geometry.lean`.

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
