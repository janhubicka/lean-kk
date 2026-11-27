# Exact age transport through one-gap padding

## Scope and interfaces

Let `g : Nat -> Nat -> Bool` be any ordinary directed Boolean table, let
`selected : Fin d -> Nat` be any terminal list, and write `a(q)=2*q+2`
for `oneGapAddress q`. Compare old columns to the meaningful terminal
coordinates `a(selected i)` in the padded table `oneGapEdge g` with old
columns to `selected i` in `g`.

The target identities are equalities of the complete raw-bound functions
and their joint canonical integer-age functions. Before the meaningful
cut `a(p)`, the padded old pool is `range (a(p))` and the unpadded old pool
is `range p`. Immediately after that same coordinate, the padded old pool
is `range (a(p)+1)` and the unpadded old pool is `range (p+1)`.

No symmetry, looplessness, forbidden-clique bound, positive number of
terminal labels, injectivity of the terminal list, or future-position
condition is needed. These are exact ordinary-table identities. They do
not construct a diary or prove that any coding event is age-neutral.

## Finite induced-image transport

First record a reusable transport independent of padding. Let `P` be a
finite old pool, `f` an injective map, and `E,F` two Boolean tables. Let
`c,c'` be their typed old columns. Assume

`F (f x) (f y) = E x y` for distinct `x,y in P`,

and `c' (f x) i = c x i` for every `x in P` and label `i`.

For every support, the common-neighbour pool inside `P.image f` is exactly
the image of the corresponding common-neighbour pool inside `P`. This is
a direct filter/image membership argument; it does not require nonempty
support or injectivity. Restricting `f` to the common-neighbour pool then
meets the hypotheses of the existing
`finiteDirectedCliqueCapacity_induced_image_eq`. Thus its exact directed
clique capacity, and consequently `ell-1-capacity`, are unchanged. Function
extensionality gives equality of the full raw-bound functions. Applying
`integerGraphAgeCanonical d ell` to that equality gives equality of the
full canonical ages. Canonicalization is not identified pointwise with
the raw bound.

This generic image lemma also supports the separate transport from event
vertex positions to actual raw graph names. Its caller must supply the
finite graph and column agreement on the actual old pool; no agreement
on unused names is asserted.

## Removing dummy rows

More generally, let finite pools `P,Q` satisfy

`a(q) in Q iff q in P` for every natural `q`.

No restriction is placed on dummy coordinates in `Q`. Fix
`T : IntegerGraphSupport d ell`. By definition, `T` has a nonempty
underlying support. If `v` survives the common-neighbour filter for the
padded columns, choose one label in that support. Its positive column
bit forces `v` to be meaningful. The inverse one-gap coordinate is then
defined with `a(oneGapIndex v)=v`; the displayed pool correspondence
places this inverse in `P`. On meaningful coordinates,

`oneGapEdge g (a(q)) (a(selected i)) = g q (selected i)`.

Every remaining column condition is therefore exactly the unpadded
condition. Conversely, an unpadded common neighbour maps to a padded
common neighbour by the same identity. Hence the padded common-neighbour
pool is exactly the address image of the unpadded common-neighbour pool.

The address map is injective and preserves every ordered ordinary atom,
so the existing induced-image capacity theorem gives the same capacity.
This proves the complete raw-bound equality, and hence canonical-age
equality, without treating the capacity as merely the cardinality of a
common-neighbour pool.

The nonempty-support argument is essential: an empty support would admit
zero-column dummy rows. `IntegerGraphSupport` excludes that case. For
`d=0`, the support type itself is empty, so full function equality is
vacuous and no nonemptiness assumption on the terminal list is added.

## Before and after a meaningful coordinate

Arithmetic gives the two required pool correspondences:

`a(q) < a(p) iff q < p`,

`a(q) < a(p)+1 iff q < p+1`.

Apply the general padding argument first with the before pools and then
with the after pools. It follows that any complete canonical-age equality
between the two unpadded prefixes transports to the two padded prefixes.
In particular the argument concerns the addition of the meaningful
coordinate itself; it does not confuse `a(p)+1` with `a(p+1)`.

## Complete old columns and no-splitting

For any two unpadded terminal names `u,v`, equality of their padded
ordinary columns on every row below `a(p)` is equivalent to equality of
their unpadded columns on every row below `p`. One direction tests only
the meaningful rows `a(q)`. In the other direction, a meaningful row has
an inverse `q<p`, and each dummy row has two false bits.

Consequently, an unpadded no-split implication on any selected list
transports to its address image: old-column equality pulls back, the
unpadded implication gives equality at `p`, and the ordinary address
identity gives equality at `a(p)`. No source/type equality, graph-freeness,
or desired padded no-split conclusion is assumed.

## Remaining application and validation

Actual coding-event age neutrality and no-splitting must be derived from
the actual coding certificates and transported to chronological vertex
positions separately. The all-auxiliaries-kept selection and its finite
seed/envelope specialization also remain separate. These transport
lemmas alone assert no legal diary parser, common inverse source, Ramsey
bound, or general-Kell resolved graph constructor.

English review: **PASS**, completed independently before Lean
implementation. The review confirmed the exact filter/image argument,
nonempty-support treatment including zero terminal labels, the distinct
before/after coordinate cutoffs, and both directions of the complete
old-column correspondence. Independent completed-source review also
**PASSED** for all twelve public endpoints. It checked the finite image
assumptions, exact capacity transport, nonempty-support argument, cutoff
arithmetic and absence of hidden graph or terminal-list assumptions.

The focused script `scripts/check_axioms_one_gap_age_transport.lean`
checks and prints the transitive axioms of exactly those twelve endpoints;
its static inventory matches the source. A normal serialized Lake run
successfully built `Kk.OneGapAgeTransport` in 2.8 seconds without a
module diagnostic; the component result is recorded in
`proof-audit/all-auxiliary-components-build.log`. No source repair was
needed. This records this module's successful build, not the entire
initial combined run or the final project gate.

Focused named-axiom execution and the final full-build/central-axiom
gates remain **PENDING**. Compiler calls are serialized by the parent
task.

## Final all-auxiliary integration checkpoint — 27 November 2026

This completed checkpoint supersedes pending validation language above.
Independent English-first, completed-source, assembly and static integration
reviews passed. The normal new-module target passed (3,624 jobs), the
normal default build passed (4,134 jobs), and the central audit/strict parser
accepted all 1,511 exact names. All 1,470 inherited names and axiom sets are
preserved. The three focused audits cover exactly all 41 new endpoints;
every axiom set agrees with central. Fourteen reports are axiom-free, and
only `propext`, `Classical.choice` and `Quot.sound` appear in the others.
Parser tests, source/import coverage and diff checks pass. See the
[completion report](all_auxiliary_envelope_completion_20261127.md) and
[machine evidence](audits/2026-11-27-all-auxiliary-envelope-completion.json)
for precise scope and the remaining controlled-retention/diary obligations.
