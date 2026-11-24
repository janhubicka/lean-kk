# Independent review: planned seeds and a common selected prefix source

Date: 24 November 2026. Independent review by the adversarial audit task of
`docs/retained_prefix_source_and_plan_seeds_english_20261124.md`, before
implementation of its proposed new generic bridge lemmas.

SHA-256 of the reviewed proposal:
`f14958f1f1888c7a1e9ca29ea6c1e5243839193a6b9b8949a95b3aac3bfc9cca`.

## Verdict

The generic exact-plan reduction and inverse selected-prefix identification
are mathematically sound. They can be formalized with the explicit hypotheses
in the English proposal. The full resolved-Q application still requires the
off-plan boringness theorem for the enlarged seed family and the concrete
record/chunk construction. Neither is discharged merely by naming the desired
retained set or by proving a generic conditional bridge.

The review inspected the published successor definitions and proofs in
`EnvelopeRun`, `EnvelopeRunExistence`, `EnvelopeInvariantLevels`,
`GPlusRetainedCodeRecovery`, `GPlusCanonicalCodeReconstruction`,
`GPlusRepresentingPairs`, and the G+ envelope pair-lifting framework, at
successor-tree-lean pin `a74c10761303a18649053f2af3a1a1697f032e13`.
It also compared the exact construction in manuscript PR132's olive
`app:independent-small-upper` subsection and the actual theorem in
`Kk/PrefixChainOrbitTransfer.lean`.

## Exact-plan reduction

For every planned i≤tau the literal ancestor of the cap U at i is an
initial seed. It therefore belongs to the actual pre-cut closure regardless
of the current selected level set, and its exact level witnesses I1. An
ordinary AlgorithmRun must select this level. The top case is supplied by
`topI`. No new retaining rule or modification of AlgorithmRun is needed.

The reverse containment follows from the stated local implication for this
same run and seed family: at an off-plan c, actual higher-stage containment
implies noninterestingness of the actual closure. Descending induction then
shows every stage is contained in the Plan. An on-plan c is harmless for this
containment whichever branch the run takes. Exact final equality follows
only after both directions have been proved.

The use of the full E1 stage invariant is correct and necessary for whole-node
coverage. At stage zero its level-range conclusion is exactly Plan together
with all levels above tau. It is not merely a statement that finitely many
crossing types can be matched. All planned seeds lie below the same actual
cap, so the singleton physical original pool represents them, and an off-plan
cut cannot be the level of an initial seed.

The enlarged X_I is a different initial seed family from
`numericHTopGenerationSeeds`. Its run and closure may differ. The proposal
explicitly retains this fact; existing corollaries specialized to the smaller
family must not be transferred without proving their premises again. Generic
whole-stage source and no-seed-at-cut lemmas remain applicable.

## Retained matrices and numerical endpoints

The k=4 real positions are p(b,r)=10b+2r. With the mandatory dummy immediately
before every meaningful base, the first missing incoming-E coordinates are
10(b−1)+1, +3, +5 and +9 for generations 1, 2, 3 and TOP. The TOP formula
really is +9. The four free cuts precede the five real positions of that
meaningful base; an intervening dummy ensures the preceding meaningful
chunk ends before this chunk begins. The anchor at 0 precedes them all.

For a retained auxiliary member there are nine retained coordinates. For a
selected coded base there are two. The cap end tau is a represented endpoint,
not an additional coordinate in the ordinary source code. Thus the displayed
ordinary code size 1+9B+2n and planned-level count 2+9B+2n are correct, provided
the stated construction makes exactly these disjoint chunks and no others.

The record determines both values of every retained ordinary edge: same
auxiliary-block edges, distinct-block nonedges, selected-terminal nonedges,
block-to-selected incidences, and earlier-code-to-later-block nonedges. The
fixed generation gate determines the numerical copies. Ordinary isolation of
odd coordinates does not erase their outgoing E relations.

For each positive-generation retained target, the marked first missing E
coordinate is retained. All incoming E bits are then determined by the strict
ordered prefix before that coordinate. Generation-zero and odd targets have
empty incoming E columns. This is an exact full retained E matrix, including
absences and reverse directions, rather than an ordinary graph-age shadow.
The retained first missing coordinate lies strictly between any E predecessor
and its target, so compression preserves the required spacing.

## Why the selected G+ orbit follows from these data

Let F cover the cap U and let U* be its actual preimage. Injectivity of the
shape map makes that preimage unique. The increasing level map and exact
range through tau enumerate Plan in order. Consequently the source cap level
is |Plan|−1, and its ordinary coordinates correspond to every planned level
except the cap endpoint.

`shapeMap_recovers_ordinaryCode` recovers all four finite ordinary tables of
U* from those retained image coordinates. The code is therefore determined
by the record's retained matrix. This ordinary code is the socle L+/E code;
it must not be confused with the full raw Kpt type including the distinguished
type vertex. The proof only needs the former at this step.

If selected target d has rank j among Plan and d<tau, the covered ancestor of
U at d has preimage the ancestor of U* at j, by preservation and reflection
of order and levels. The strict representing pair consisting of that source
ancestor and U* represents the prefix of the recovered ordinary code of size
**j+1**. The actual representing-pair action maps it to the prescribed target
pair. Thus the target is an honest monoid image of the common prefix vertex,
not just a code with the same age or a comparable length.

For two occurrences of the same record, equal retained matrices and equal
selected chunk ranks give equal source prefix codes label by label. Their
strictly increasing sizes supply injectivity. These common selected prefix
vertices are exactly what `prefix_chain_orbits_colour_factors` requires.
That transfer does not additionally require equal whole raw parameter sets
or minimality of the enlarged envelope. Full parameter-closure control still
belongs in the proof that the chosen omitted cuts are boring.

The treatment of records with no occurrence is also necessary: either index
only the occurring finite records, or build a valid source directly. Choosing
an occurrence without treating empty fibres would be invalid. The proposal
states both legitimate alternatives and does not make that choice silently.

## Limits to preserve during implementation

The exact Plan must be an explicit finite set derived from the record's
concrete chunk data. An arbitrary payload described as a record does not
supply the matrix equality. The run must use X_I itself, with all its new
seeds. Whole-node E1 coverage, strict selected position below tau, exact
source/target level bookkeeping and both Boolean values of every retained
atom must remain in the bridge. The output is a common **selected G+ prefix
source**; it should not be labelled a proof that every compressed Kpt closure
parameter is record-determined. Global upper canonisation follows only after
the actual off-plan and construction hypotheses have been established.
