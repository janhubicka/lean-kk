# Exact prefixes and the countable individual-event schedule

## Starting data and scope

The finite event extraction starts from the existing actual fair rounds.
Its events retain their concrete pre-old pool, positive finite block,
actual post-event edge table, and full marker/cover/coding witnesses.
A chain compares those tables with one reference graph only on each
event's post-old pool together with the round's original live set.

This layer derives exact finite prefixes and constructs a new countable
schedule from those extracted events. It does not change the older
numerically sorted round schedule. It does not assume an event schedule,
an arbitrary ordering of auxiliary names, or global equality of tables
on unused names.

## Finite chain consequences

Induct on the event chain. At one step the new block has no repetitions
and is disjoint from its pre-old pool; the next pool is exactly their
union. Thus the flattened list of all block entries is repetition-free,
disjoint from the initial pool, and contains exactly the final pool minus
the initial pool.

The pre-old pool of the event at index j is exactly the initial pool
union all blocks at indices below j. This follows by the same induction:
the zero index is the initial pool, and passing a head adds precisely its
block. It also proves pairwise disjointness of distinct event blocks.
Every event retains its original certificate and its localized agreement
with the chain's reference graph.

## Ordered tagged positions

For any positive finite batch lengths, the existing tagged-position map
is ordered lexicographically: the position of (m,i) precedes that of
(n,j) exactly when m<n, or m=n and i<j. Different batches are separated
by their strict boundary inequalities, and inside one batch cancellation
of the common boundary reduces to the index comparison.

Consequently the prefix before a specified tagged entry is exactly all
earlier batches together with the entries of its own batch at smaller
indices. This statement uses the already proved position/location inverse
and actual list membership, including all empty prefixes.

## Two successive countable enumerations

For each fair round choose the finite extracted event list. Each list is
nonempty because it ends in a singleton coding event. First enumerate
these lists with the existing countable finite-batch bijection; this gives
a global natural-number index for every event occurrence, in round order
and in its actual within-round order.

Next enumerate the vertex blocks of those events. Every block is positive,
so the second countable finite-batch bijection applies. Its event-boundary
prefix is the union of exactly the earlier event blocks. The finite chain
prefix theorem and the exact old-pool union across earlier rounds identify
this union with the actual current event's pre-old pool, provided the
initial fair-stage pool is empty. Inside an event, a vertex prefix adds
exactly an initial segment of that event's own block.

Distinct event occurrences have disjoint blocks: within a round this is
finite-chain freshness; across rounds it follows because their vertices
belong to disjoint successive old-pool differences. Each block is itself
repetition-free. Therefore the vertex enumeration is injective and has
range exactly the actual fair-limit domain.

## Graph and coding transport

Every event post-old pool lies inside its round's terminal old pool.
Every member of the round's original live set is either the newly coded
vertex, now old, or a member of the next live set. The existing fair-limit
edge-preservation theorem therefore transports all localized event
agreements to the single actual fair-limit graph. The actual event edge
tables and certificates remain unchanged.

The code event is last in its round and its block is the singleton of the
prescribed even original. Its global event position and then its global
vertex position give the coding position; these increase strictly with
the round. Pulling back the fair-limit graph along the injective vertex
enumeration preserves symmetry, loop-freeness and K4-freeness, and its
coding positions induce exactly the prescribed original graph.

## Paired dummy coordinates

Give each auxiliary block its global event occurrence index, not its
essential support or numerical vertex names. Its entries occupy one
interval of ordinary chronological positions. After replacing each
ordinary position by its gap/original pair, all meaningful coordinates
between two members still belong to that same event; intervening odd
coordinates are dummies. This proves the required block convexity modulo
dummies for any flag that retains or omits a whole event block.

The argument establishes actual event order, exact prefixes, and block
geometry. The projected canonical diary operations, finite record bounds,
ordinary hypotheses at omitted real cuts, common full inverse sources,
history occurrence and sharp Ramsey bounds remain separate obligations.

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
