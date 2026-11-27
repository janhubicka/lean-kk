# Finite selection of the actual coding coordinates

## Source and scope

This construction starts from main
`be958e2f83b9d962dc641fddc5b2ccca632af051` and its actual individual-event
schedule. It identifies the padded coordinates of coding events with
the prescribed original indices, then constructs a keep flag from a
finite selection of those indices. The desired correspondence is a
conclusion, not an additional premise.

Write `J(n)` for `resolvedFairCodingEvent s0 n`, `p(n)` for
`resolvedFairEventCodePosition s0 n`, and `a(n)` for
`oneGapAddress (p(n))`. The proposed public name for the latter map is
`resolvedFairOriginalAddress`.

The generic inverse-coordinate statements retain the explicit
assumption `hEmpty : s0.old = empty`, because the current event-vertex
injectivity interface uses that assumption. For the actual initial
stage the proof is definitionally `rfl`. The construction remains
K4-specific through the existing fair-round constructor.

## English proof before Lean implementation

### The role at an original's actual address

The code position `p(n)` is the vertex-batch boundary of the event
`J(n)`. Every event block has positive size. Thus this boundary belongs
to exactly that event's half-open interval, by the proved batch-index
characterization. This gives
`resolvedFairVertexEventIndex s0 (p(n)) = J(n)`.

The coding-event specification says that this event has code kind and
block `[2*n]`. The existing formula for roles at meaningful coordinates
therefore gives, for every keep flag,
`resolvedFairEventRole s0 keep (a(n)) = coded (keep (J(n)))`.
This direction needs no empty-initial-pool assumption.

The map `a` is strictly increasing: it is the composition of the
already strictly increasing coding-position and one-gap-address maps.
In particular it is injective.

### Recovering the original index of every coded coordinate

Suppose a coordinate `v` has role `coded b`. The existing coded-role
characterization says that `v` is meaningful and that the event `k`
containing its unpadded position `oneGapIndex v` has code kind. Let `n`
be that event's round index, obtained from `resolvedFairEventLocation`.

The actual event certificate is a certificate for coding the original
`2*n`. The proved `ResolvedEventCertificate.code_block` theorem therefore
identifies its block with `[2*n]`. The enumerated vertex at
`oneGapIndex v` belongs to that block, so it equals `2*n`.

The existing coding-position theorem also identifies the enumerated
vertex at `p(n)` with `2*n`. Injectivity of the actual event-vertex
enumeration, using `hEmpty`, gives `oneGapIndex v = p(n)`. Since `v` is
meaningful, the inverse address identity gives `v = a(n)`.

Applying the event-index identity from the previous step identifies
`k` with `J(n)`, so its flag is exactly `keep (J(n)) = b`. Conversely,
those two equalities imply the coded role by the address-role theorem.
Strict increase of `a` makes the recovered original index unique.

This proof uses the actual singleton coding certificate and actual
enumeration injection. It assumes neither a proposed list of coding
coordinates nor that all coded coordinates are already in the image
of the desired map.

### A keep flag constructed from a finite original selection

Let `S` be a finite set of original indices, and let `auxKeep` be an
arbitrary flag on global event occurrences. Define
`resolvedFairSelectedKeep s0 S auxKeep k` as follows:

* if the actual event `k` is coding, keep it exactly when
  `k` belongs to the finite image `S.image J`;
* otherwise use `auxKeep k`.

This is one flag per complete event, so it preserves whole-block
retention. Since `J` is strictly increasing and hence injective,
membership of `J(n)` in that finite image is equivalent to `n in S`.
The coding-event specification then gives
`resolvedFairSelectedKeep s0 S auxKeep (J(n)) = decide (n in S)`.
The value at every auxiliary event is exactly `auxKeep k`.

Combining this flag identity with the derived inverse-coordinate
theorem proves the intended exact selection statement:
the role at `v` is `coded true` if and only if there exists `n in S`
with `v = a(n)`. This holds for arbitrary finite `S`, including empty
`S`; no nonemptiness premise is introduced.

As a useful finite bound, every such coordinate is strictly below
`S.sup a + 1`. This follows directly from the proved correspondence
and the finite supremum property, rather than from an assumed bound
on the coding positions.

### Exact ordinary bits at the selected addresses

The original-address ordinary edge table is unchanged:
`oneGapEdge (resolvedFairEventEdge s0) (a(i)) (a(j))`
equals `s0.edge (2*i) (2*j)`. Apply `oneGapEdge_address` and the already
proved `resolvedFairEventEdge_originals`. The equality includes the
diagonal. For an actual initial stage, it specializes to the input
graph bit `E i j`.

## Planned public interfaces

The new module is `Kk.ResolvedFairCodingSelection`. The main names are:

* `resolvedFairOriginalAddress` and its strict-monotonicity theorem;
* `resolvedFairVertexEventIndex_codePosition`;
* `resolvedFairEventRole_originalAddress`;
* `resolvedFairEventRole_coded_iff_originalAddress`, with arbitrary
  Boolean flag, and its unique-original corollary;
* `resolvedFairSelectedKeep`, its code and auxiliary value theorems;
* `resolvedFairSelectedRole_coded_iff`, identifying the exact finite
  selection;
* a finite supremum bound and the exact original-address edge table.

The selected-front enumeration and the finite retained level/pool plan
are separate modules. They may use the exact role correspondence to
identify their coded entries with `S`, and strict monotonicity to bound
the selected-front cardinality by `S.card`.

## Cap convention and remaining application work

When the finite retained pool includes an actual coding cap, the cap's
original index must belong to `S`. It is then a genuine member of the
selected coding front. No zero-old-column assertion is made for that
cap merely because it is an additional endpoint. The separate retained
plan uses this membership to retain the cap's entire gap/original pair.

The correspondence does not construct a projected diary, prove
selected-age neutrality or no-split, identify common inverse sources,
establish arbitrary-history occurrence, or prove a Ramsey bound. The
finite-front and envelope adapters still expose their genuine
remaining hypotheses.

This English proof passed independent review before Lean implementation.
The review confirmed that singleton coding certificates and injectivity
derive the converse, and that the finite-image keep definition introduces
no desired-correspondence premise. The completed source also passed
independent scope reviews without a semantic correction.

## Local validation

The first serialized direct Lean check of
`Kk.ResolvedFairCodingSelection` passed with exit code zero in 3.667
seconds and an empty diagnostic log, using the pinned Lean 4.35.0-rc3
toolchain. All eleven public theorem endpoints compile; the source
required no compiler repair.

The focused script
`scripts/check_axioms_resolved_fair_coding_selection.lean` names every
one of those eleven endpoints with both `#check @` and `#print axioms`.
At this direct-check checkpoint, the full normal project build and
focused/central transitive-axiom gates remained pending. Their final
status is recorded in the batch integration evidence.

## Final finite-front integration checkpoint — 27 November 2026

This completed checkpoint supersedes pending validation language above.
The normal new-module target passed (3,619 jobs), the default project build
passed (4,129 jobs), all four focused Lean audits and strict parsers passed,
and the central audit accepted all 1,470 exact names, including every one
of the 76 new endpoints. All 1,394 inherited names and axiom sets are
preserved. Only `propext`, `Classical.choice` and `Quot.sound` appear, with
fourteen central names axiom-free. Parser tests, source/import coverage
and diff checks pass. See the [completion report](finite_selected_front_completion_20261127.md)
and [source-hash/axiom evidence](audits/2026-11-27-finite-selected-front-completion.json)
for the precise conditional envelope and remaining application obligations.
