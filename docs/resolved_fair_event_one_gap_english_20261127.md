# The actual event chronology in the canonical one-gap source

## English proof before implementation

Use the newly constructed `resolvedFairEventEdge s0`, whose vertices
enumerate actual individual marker, cover, and coding blocks in order.
Assume explicitly that `s0.old` is empty, as required by this scheduling
interface. The event-vertex enumeration is injective, so the pulled-back
graph is K4-free; symmetry and absence of loops also hold. The increasing
positions `resolvedFairEventCodePosition s0 i` induce the original graph
on the even names `2*i`.

Apply the existing finite-clique-bound-to-forbidden-avoidance theorem,
then the already proved `oneGapPartial_avoids` theorem. This constructs
the genuine one-gap partial structure for the new chronological graph
and its avoidance proof. Apply its canonical `toGPlus` map at the
one-gap address of each coding position. No representation map or
resolved graph is assumed.

The source size of original `i` is exactly twice its coding position
plus three. These sizes strictly increase, hence the canonical sources
are distinct. For distinct originals, the canonical binary-atom theorem
and `oneGapEdge_address` recover both ordinary directions, including
nonedges, as `s0.edge (2*i) (2*j)`. The diagonal atom is false. The
canonical auxiliary-atom theorem and strict increase of coding positions
give exactly `decide (i < j)` for all pairs of originals.

For `s0 = resolvedInitialStage E hFree hSym hLoops`, the empty-old-pool
proof is `rfl`, and `s0.edge (2*i) (2*j) = E i j`. Thus the application
to an arbitrary symmetric, loop-free K4-free graph E requires no extra
initial-pool assumption.

## Interface and remaining scope

The new module `ResolvedFairEventOneGap` is separate from the older
round-sorted `ResolvedFairOneGap`. Its generic avoidance and canonical
source definitions expose `hEmpty : s0.old = ∅`; that proof does not
alter the underlying edge or address data.

The module supplies actual canonical sources and their exact ordinary,
diagonal, and auxiliary atoms for the individual-event chronology.
It does not assert projected diary-record preservation, equality of
envelope source codes, a common inverse-source orbit, arbitrary-history
occurrence, or a big Ramsey bound. Those require additional theorems.

This proof plan passed independent review before Lean source
implementation. The completed source also passed an independent
scope review without a semantic correction.

## Local validation

`Kk.ResolvedFairEventOneGap` passed its serialized direct Lean check
with the pinned Lean 4.35.0-rc3 toolchain, exit code zero, and an empty
diagnostic log. All eight public theorem endpoints compile. The only
repair replaced a rewrite through an inline empty-pool proof with an
explicit theorem application and transitivity; no statement or premise
changed.

The focused script `scripts/check_axioms_resolved_individual_events.lean`
covers all 24 public theorem endpoints in `ResolvedEventTrace`,
`ResolvedRoundEvents`, and `ResolvedFairEventOneGap`. At this local-check
checkpoint, the full normal project build and the focused and central
transitive-axiom gates remained pending. Their final status is recorded
in the batch integration evidence.

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
