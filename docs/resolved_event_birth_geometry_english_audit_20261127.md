# Ordinary edges at the birth of actual resolved event blocks

## English proof before Lean implementation

An actual `ResolvedEventCertificate` retains the event's own edge table
and its marker, cover or coding witness. Derive its birth-edge facts from
that witness; no old-to-new zero-edge premise is added.

For a marker event, the new block is the singleton marker `q_i` and the
pre-old pool is the original stage's old pool together with a subset `R`
of the same marker batch. The original old pool is disjoint from the live
set `W`. Every marker name is odd, whereas all live names are even, so
`R` is disjoint from `W` as well. The actual marker edge definition links
`q_i` only to live names in its own class passing its Boolean test.
Consequently its edge to every pre-old name is false. Symmetry of the
actual marker-stage edge table gives the reverse direction.

For a cover event, the new block is the sorted fresh set `Q`. If `p` is
pre-old, disjointness gives `p notin Q`, and stage separation gives
`p notin W`. The `blockEdge` definition therefore makes every edge between
`p` and a member of `Q` false. Distinct members of `Q` have both directed
edge bits true. A member of `Q` is adjacent to a live name `v` exactly
when the actual live label of `v` belongs to the actual support `T`.

Coding events are excluded from the old-to-block zero theorem: the coded
original may be adjacent to old names. Their blocks are singletons, as
are marker blocks. Thus every event block is internally a directed clique:
the assertion is vacuous for marker/coding singletons and follows from
the block definition for cover events. The actual stored event edge
table is symmetric and loop-free in all three cases.

## Integration boundary

The essential conclusion is that every non-code certificate supplies
both ordinary zero bits between its actual pre-old pool and its actual
block. It concerns the stored `event.edge`. Transport to the single
fair-limit graph requires the separate, already specified agreement on
the event's post-old/live domain. No agreement on unused names is needed
or asserted.

Together with exact chronological pre-old prefixes, this supplies the
birth fact used to prove that an earlier coded vertex has no edge to a
later auxiliary block, and that distinct auxiliary blocks have no edges
between them. Those global chronological consequences require the actual
event schedule and its domain agreement; they are not assumed as inputs
to the birth theorem.

The independent English-proof review passed before implementation. It
checked the marker positive-neighbour equivalence, the cover edge
definition, the complete pre-old/live separation, and the necessary
exclusion of coding events from the zero-edge conclusion.

The subsequent independent review of all ten source endpoints also passed.
It verified that the stored event edge table and actual support witnesses
remain unchanged and that the global chronological consequences are left
to the separate transport layer.

## Local validation

The direct serial Lean check of `Kk/ResolvedEventBirthGeometry.lean` passed
with exit code 0 on Lean 4.35.0-rc3. All ten public endpoints compiled;
the check produced no warnings. The log is
`proof-audit/ResolvedEventBirthGeometry-local.log`.

Named transitive-axiom validation: **PENDING**.

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
