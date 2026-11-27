# Individual events extracted from actual resolved rounds

## Scope and source

This construction starts with the actual `ResolvedRoundResult` and
`ResolvedRoundTrace` witnesses already built on main
`141059fb223ceed0b1e53b5fb9d160f4938b2c53`. It derives a finite ordered
list of individual marker, cover, and coding events. No desired event
list, chronology, or increasing allocation of names is an input.

The older `ResolvedFairChronological` sorts all auxiliary names in a
round. That order does not identify the recorded cover-path order:
the freshness theorem exposes disjointness from the current old and
live sets, but does not expose a numerical ordering between successive
fresh blocks. The construction here uses each recorded cover block
in path order. Numerical sorting is used only inside one cover block,
or to choose an arbitrary order for independent private markers.

## Proposed finite interface

An event has four data fields: its kind (`marker`, `cover`, or `code`),
its finite preceding old pool `preOld`, its finite list of newly old
vertices `block`, and the actual edge table `edge` after that event.
Its resulting old pool is defined as
`postOld = preOld union block.toFinset`.

`ResolvedEventCertificate W r e` retains the actual witnesses for the
event. A marker certificate stores the original bare stage, class map,
Boolean test, safety and exact-class certificates, the previously
inserted subset of the marker batch, and the next mixed class. A cover
certificate stores the live stage, fresh block, support, safety budget,
actual insertion endpoint, age cover, changed coordinate, minimality,
and size equation from `ResolvedLiveCoverPath.advance`. A code
certificate stores the saturated terminal live stage and its exact
class, singleton, and constant-adjacency certificates, with the coded
vertex in the live set. Thus these are actual event certificates,
not just kind labels attached to a partition of the final pool.

The round's live set `W` is kept as a fixed reference set in the finite
chain. Marker and cover events leave it live. The final code event
moves `r` from `W` into the old pool; the actual next live set is
`W minus {r}`, exactly as specified by the original round trace.

`ResolvedEventChain W r E P events Q` is an inductively defined
proposition. Its empty case has no events and identical endpoint
pools. Its nonempty case starts at the head event's `preOld`, stores
the head event certificate, proves agreement of the reference graph
`E` with the event's edge table on `postOld union W`, and continues
from the head event's `postOld`. In particular, this is a finite
sequence with exact intermediate pools by construction.

The primary extraction statement has the following shape. Given
`h : ResolvedRoundResult s r t` and `r in W`, there exist an auxiliary
event list `aux` and one code event `code` such that:

* `ResolvedEventChain W r t.edge s.old (aux ++ [code]) t.old`;
* every event in `aux` is a marker or a cover;
* `code.kind = .code` and `code.block = [r]`.

Every certified block is nonempty, has no repetitions, and is disjoint
from its own preceding old pool. These properties imply that the
concatenated vertex list is repetition-free and disjoint from the
initial old pool. The concatenated list adds exactly `t.old minus s.old`.
Its final vertex is the coded original `r`.

## Marker serialization

Take the actual finite set of private markers of one recorded batch.
List those names in increasing numerical order. Its list has no
repetitions and contains exactly the marker set. An empty marker set
contributes no events.

Suppose the previously listed markers form `R`, and the next name is
the marker `q` of mixed class `i`. The injectivity of marker names and
list distinctness give `q notin R`. The exact old pool immediately
before this event is `s.old union R`; immediately after it, it is
`s.old union R union {q}`. The batch's final graph restricted to either
of these pools and the whole live set is a valid intermediate graph:
it is a restriction of the already proved K4-free batch graph.

The existing `refineBatch_single_split` theorem applies to exactly this
subset `R`. It supplies live witnesses on opposite sides of the test
whose entire preceding old columns agree, and identifies the marker's
positive live neighbourhood with the positive child of that actual
preceding class. Edges on the original `s.old union W` domain agree
with the original stage. Previously inserted marker columns are read
from the same batch table and therefore stay fixed. The new marker is
anticomplete to the preceding old pool, including the other already
inserted markers. These facts follow from the actual marker edge
definition and the freshness of every marker.

The event's graph table is the batch's final table. Its values on names
not yet old or live have no chronological significance. On the actual
domain, the event is the genuine one-marker restriction described
above; no equality of whole graph tables across later insertions is
asserted.

An induction on the marker list builds the event chain. The induction
invariant is that `R` is a subset of the batch, the remaining list is
disjoint from `R`, and the current old pool is `s.old union R`.
Taking `R` empty produces the required whole-batch chain.

This certifies genuine class splitting. It does not by itself certify
the complete canonical diary split-age operation, a lexicographic
order of the two children, or a projected record parser.

## Cover serialization

Induct on the actual `ResolvedLiveCoverPath` proof. A stop contributes
the empty event list. At an advance, retain its actual block `Q` and
all its support and cover certificates. Add one event with block
`Q.sort`, then append the list extracted recursively from the tail.

The block is nonempty. Otherwise `Q` is empty, and the definitions of
`insertBlock`, its columns, and its old pool give unchanged old age,
contradicting the recorded strict change at the support `T`. Thus no
empty event is passed to a positive-block enumeration.

The pre-pool is the recorded stage's actual old pool; the post-pool is
that pool union `Q`, literally the old pool of its insertion endpoint.
The block is a clique, anticomplete to the pre-pool, and has precisely
the recorded support columns on `W`. All these assertions concern the
actual insertion table, not a separately chosen realization.

Two small consequences of cover-path induction are needed: monotonicity
of the old pools and preservation of every edge on the starting
old-plus-live domain. At an advance, these use union inclusion and
`insertBlock_preserves_live`, then the induction hypothesis for the
tail. These lemmas justify transporting each event to the terminal
graph only on its actual post-pool and `W`.

An interior vertex prefix of this one cover event has old pool equal
to the recorded pre-pool union the corresponding initial segment of
`Q.sort`. Hence it is a literal partial insertion of that one block.
The later scheduling layer can make these blocks contiguous without
reordering the cover path or relying on numerical freshness.

## Assembling one round

Destructure the existing round trace. It gives the first marker batch,
the second marker batch, the equality of the second batch endpoint
with the initial labelled cover stage, the actual cover path, and its
saturated terminal stage. Serialize the two marker batches in that
order, then the cover path, then append the singleton code event.

The marker-preservation theorem and the cover-path preservation lemma
show that the terminal graph agrees with every earlier event graph on
that event's post-pool plus `W`. The round trace identifies this graph
with `t.edge`. Pool equalities identify the adjacent endpoints, so
chain concatenation gives exact intermediate pools from `s.old` to
`t.old`. The code is fresh for the terminal pre-pool because it is still
live there. Saturation, singleton isolation, and constant adjacency
give the existing coding age-neutrality and no-split conclusions.

Empty marker batches and a zero-step cover path cause no problem:
they contribute no events. The final singleton code ensures that the
round's event list, and its flattened vertex list, are nonempty.

`ResolvedLiveCoverPath` and the round witnesses live in `Prop`. Their
induction therefore proves an existential serialization proposition.
An actual chosen event list is obtained afterwards by `Classical.choose`.
There is no elimination from a proof directly into list data.

## Later countable scheduling layer

Applying the finite extraction to each actual fair round gives positive
finite lists of positive event blocks. A generic finite-list prefix
argument, followed by the existing countable finite-batch schedule,
can concatenate these lists while preserving each event as a consecutive
block. Exact old-pool recurrence identifies every event boundary with
the corresponding actual old pool. Fair-limit graph preservation
transports the localized event certificates into the limit graph.

This closes the absence of individual-event chronology. It does not
assert the projected canonical diary parser, a common inverse-source
orbit, arbitrary-history occurrence, or the final big Ramsey bounds.

## Minimal API additions

All planned additions can live in new modules `ResolvedEventTrace`
and `ResolvedRoundEvents`. No existing theorem needs a stronger premise
or a weaker conclusion. The additional elementary APIs are:

* event certificate consequences: block positivity, distinctness,
  and freshness;
* cover-path old-pool monotonicity and localized graph preservation;
* cover-block nonemptiness from the recorded strict age change;
* finite chain concatenation and localized graph transport;
* existential marker-batch, cover-path, and round serialization.

This English proof was written before implementation and passed an
independent adversarial review. The review emphasized that reference
graph transport keeps every event's own edge table unchanged, and
that the code's post-pool intersects the fixed reference live set at
the coded vertex. No generic post-pool/live disjointness is claimed.
Lean validation status will be recorded separately.

The core interface retains the actual birth geometry in its constructor
witnesses. The companion `ResolvedEventBirthGeometry` module exposes
named theorems for symmetry, loops, auxiliary-old zero edges, block
cliques, live columns, and marker/coding singletons by eliminating those
certificates and using the existing marker and block edge lemmas.

## Local validation

`ResolvedEventTrace` and `ResolvedRoundEvents` passed serialized direct
Lean checks with the pinned Lean 4.35.0-rc3 toolchain and no warnings.
The finite extraction required only elaboration repairs: explicit
function equalities for the empty-block age calculation, explicit
membership lambdas, normalization of finite-set/list expressions, and
explicit unfolding of event post-pools. No theorem statement or
certificate premise was weakened.

The dependent `ResolvedFairEventSchedule` and
`ResolvedEventBirthGeometry` modules also passed their local Lean
checks. The focused script
`scripts/check_axioms_resolved_individual_events.lean` covers all ten
public core-trace theorems, all six round-extraction theorems, and all
eight event one-gap source theorems. At this local-check checkpoint,
the full normal project build and the focused and central transitive-axiom
gates remained pending. Their final status is recorded in the batch
integration evidence.

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
