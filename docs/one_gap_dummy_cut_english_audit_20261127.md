# Omitted dummy cuts in the actual one-gap structure

## English proof before Lean implementation

Let `G` avoid the normalized Henson forbidden family for `ell >= 2`, and
let `A = (oneGapPartial G).finitePrefix N`. The ordinary coordinates are
the positive even numbers. Every other coordinate is an isolated dummy.
Fix a positive dummy cut `c < N` and the complete retained ambient-original
pool `V`, including any retained auxiliary originals and the cap.

Both ordinary bits between `c` and any original are false by the definition
of `oneGapEdge`. This is a statement about the new cut row and column.
Future retained originals may have nonzero columns at earlier coordinates.
In particular, putting an empty selected list into the existing nonselected
old-column-zero condition would be incorrect.

Suppose two actual originals are eligible at `c`, meaning that both free
levels are at least `c+1`, and their complete old types agree. Equality of
old types gives all old ordinary-column equalities. The two new cut bits
are both false. Symmetry and neutral loops/diagonals follow from avoidance
by `G`, while genuine free-level eligibility fixes the forward and reverse
auxiliary bits. The existing atom-extensionality theorem therefore gives
equality of their complete next types. No full-type coherence premise is
assumed.

Construct `F = oneGapRetainedPoolData A c V` using the existing eligible-pool
construction. Every chosen target comes from an actual eligible retained
original, and its cut bit is false. The no-positive theorem proves full
corrected B3: a new forbidden clique must contain the restored cut and an
upper vertex, whose required positive cut bit contradicts isolation; the
loop and asymmetry cases follow from the already established full B3
lemmas. This applies when the source is empty and when it contains cap or
auxiliary types. No selected labels, selected age equality or source
nonemptiness premise is needed.

Every target is admissible as an actual ambient prefix. Derived next-type
coherence makes the prescription cover every crossing of any set contained
in the complete retained prefix pool. The prescribed-extension theorem
then constructs a genuine monoid map skipping just `c` with the required
action on all those crossings.

## Endpoints require complete retained pairs

Zero cut bits do not alone exclude a closure endpoint. The exact free-level
formula is `v-1` at a meaningful original and `0` at a dummy original.
For `c > 0`, equality `freeLevel(v) = c` forces `v = c+1`. For example, the
original at `v=4` ends at the dummy cut `c=3`. This original is ineligible
for the crossing prescription at `3`, but can still witness the endpoint
test. Crossing coverage must not be used to infer endpoint exclusion.

Retain the anchor and complete pairs for a finite set `S` of ordinary
indices:

```text
I(S) = {0} union {2*i+1 : i in S} union {2*i+2 : i in S}.
```

Every meaningful retained coordinate has its preceding gap in `I(S)`.
The free endpoint of every retained ambient name therefore belongs to
`I(S)`: use its preceding gap for a meaningful name and the retained
anchor for a dummy name. Thus no original in a pool of retained names
ends at an omitted cut. More generally, the same conclusion follows from
`0 in I` and the concrete pair-retention hypothesis
`real v -> v-1 in I` for every original in `V`.

With seed levels retained, the derived endpoint condition and complete
next-type coherence invoke the existing no-meet theorem. The exact closure
normal form excludes every endpoint of the full planned closure, including
successor parameters and iterated meets; meet closure also excludes I2.
All parameter originals must still be covered by `V`.

## Assembly and scope

The planned-envelope construction can now split on the cut coordinate.
At a meaningful omitted cut use the existing selected-positive,
selected-no-split, nonselected old-column-zero and complete selected-age
hypotheses. At a dummy omitted cut use the direct construction above.
Consequently none of those selected hypotheses is required at dummy cuts.
The retained-pool coverage, seed retention and pair-retention conditions
remain explicit. The anchor is retained, so every omitted cut is positive.

This supplies a direct dummy-cut branch and its finite-pair endpoint
arithmetic. It does not construct the individual event diary, verify the
meaningful-cut hypotheses for every projected event, or identify a common
inverse source. The local Henson argument applies to every `ell >= 2`;
it does not generalize the separate K4 fair-graph constructor.

## Adversarial review

The independent proof audit accepted the argument before implementation.
It checked the `c=3, v=4` endpoint counterexample, the distinction between
zero new cut bits and potentially nonzero old columns, and the empty-source
and nonempty-cap cases of corrected B3. These distinctions are part of the
theorem contracts and are not discharged by crossing coverage alone.

The subsequent independent review of the complete source also passed. It
checked the meaningful-cut guards on all four selected hypotheses, the
separate endpoint derivation, and the actual full-closure and prescription
theorems invoked by the assembled envelope proof.

## Local validation

The normal target `lake build Kk.OneGapDummyCut` passed with exit code 0
on Lean 4.35.0-rc3 (3,523 jobs). All fourteen public endpoints, including
the assembled envelope theorem, compiled. The log is
`proof-audit/one-gap-dummy-cut-build.log`.

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
