# Track G — transport physical bad-cut support across different source coordinates

**16 November 2026, English proof and hostile audit before Lean.**

## Source and novelty audit

This is a genuinely distinct successor to verified Track E E54/E55 and merged
Track G #230. E55's `kptPhysicalBadCuts_eq_of_two_failure_flags` assumes the
**same** source-coordinate cut in both occurrences. That is not enough when a
realization of a diary stretches or inserts levels into a numerical-H+
presentation. We must distinguish three questions:

1. Can physical bad-cut **sets** be transported along an explicitly supplied
   source-coordinate map `f`? (This note: conditional yes.)
2. Does the resolved diary actually construct `f`, preserve the relevant
   old-boring predicate and the terminal/full-dependent-L+ failure flags,
   and exclude extra bad cuts outside the image? (**Unproved geometry**.)
3. Does equal bad-cut support yield a common labelled Kpt envelope orbit?
   (No; it forgets node multiplicity, assigned upper types and MMap action.)

We reuse E55's independently checked definitions:
`KptPhysicalTerminalFailure`, `KptPhysicalCrossingFailure`,
`KptPhysicalCutFailure` and `kptPhysicalBadCuts`. The last is the finite
set of cuts `c<top` skipped by the old run for which at least one flag
holds. Unlike E54's indexed definition it does **not** depend on any
enumeration of finite source nodes.

## Theorem G-reindex — exact image of the intrinsic bad-cut set

Let `family` be one fixed normalized forbidden family, with two
independent old/new physical source families and two old-selected
predicates `selected₁, selected₂`. Write `top₁,top₂` for their finite
old scan horizons. Let `f : Nat → Nat` be a proposed source-cut
coordinate map. We assume:

- **range:** for every `c<top₁`, one has `f(c)<top₂`;
- **old-boring equivalence on image:** for every `c<top₁`,
  `c∈selected₁(c) ↔ f(c)∈selected₂(f(c))`;
- **separate physical flag equivalences on image**, at each
  `c<top₁`: the OLD→NEW terminal-failure flag is equivalent at
  `c` and `f(c)`, and likewise the complete same-node old/upper
  dependent L+ crossing-failure flag;
- **off-image quietness:** at any `d<top₂` with no preimage
  `c<top₁`, if `d` is old-boring, then the actual physical failure
  predicate is false there.

Then
```
Bad₂ = (Bad₁).image f.
```

**Proof:** For a bad target cut d, the off-image quietness hypothesis
rules out having no preimage, so choose c<top₁ with f(c)=d.
The old-boring and both failure-flag equivalences transport
the source-badness test backward, proving c∈Bad₁. Conversely, for
c∈Bad₁, the range, old-boring and separate flag equivalences
prove f(c)∈Bad₂. The E55 normal-form membership theorem supplies
the exact conjunctive conditions; no node-by-node bijection or
pointwise equality of numerical positions is assumed.

**Uniform cardinal consequence:** `card Bad₂ ≤ card Bad₁ ≤ top₁`,
because the image of a finite set has at most its original
cardinality and Bad₁ is a subset of the finite interval
`Finset.range top₁`. Importantly **injectivity is not needed** for
this bound. An actual successor-tree cut normalization should
add order/prefix compatibility separately; this elementary set
transport theorem never asserts an arbitrary map f is geometric.

In the future take Bad₁ from a fixed finite representative of
a fully refined diary Θ and write `f_e` for the map into occurrence e.
Only after constructing the maps and verifying all four conditions
can we conclude the number of bad cuts is uniformly bounded by
the representative's finite top. We do NOT yet have the premises.

## G-reindex with permitted extra microcuts (more useful stagewise form)

The preceding no-off-image-failure hypothesis is too strong for a
resolved-copy stage that intentionally adds genuine auxiliary
microevents outside the transported old source-cut template.

Fix a **finite** set `Extra` of *permitted* new physical cut coordinates,
which includes all intentionally new auxiliary I1/I2/I3/B3 microcuts.
Keep the range and on-image old-boring/terminal/crossing failure-flag
equivalences from G-reindex. Replace off-image **quietness** by the weaker
condition: every old-boring target cut outside the image which carries a
physical terminal or complete paired-L+ crossing failure belongs to
`Extra`.

Then, directly from the E55 membership normal form,

```
Bad₂ ⊆ (Bad₁).image f ∪ Extra,
card Bad₂ ≤ card Bad₁ + card Extra ≤ top₁ + card Extra.
```

Proof: a bad target cut with a preimage transports to Bad₁ as before;
a bad target cut without a preimage lies in Extra by the new assumption.
Finite-set inclusion gives the first cardinal inequality, followed
by the elementary union and image cardinality bounds. **No
injectivity of f or equality of finite source-index sizes is
needed.** If `Extra=∅`, this becomes the original exact-image result.

**Named sharper Lean consequence.** The stagewise statement
`kptPhysicalBadCuts_card_le_reference_bad_add_extra` gives the
direct recurrence `|Bad₂|≤|Bad₁|+|Extra|` without replacing the
reference bad-cut count by its scan height. This is the bound one
can telescope through a finite sequence of correctly aligned
resolved-diary stages once their finite `Extra` sets are actually
bounded. The weaker `|Bad₂|≤top₁+|Extra|` is a corollary, not
the basic inductive estimate.

This is preferable for an inductive resolved-diary construction:
each legitimate microevent may add a bounded number of extra bad
cuts. However, the theorem does **not** prove that the permitted
new extras are uniformly bounded by the diary, or that the
physical sources satisfy the stated off-image classification.
Without those geometric facts the cardinal inequality is only
conditional. A template of the form `Extra=Finset.range top₂`
would make it useless; this must not be advertised as a BRD bound.

## Hostile audit

1. **Vacuity check:** `f(c)=c` between genuinely different runs is
   *not* established. The E55 same-coordinate result cannot be
   applied blindly.
2. An arbitrary `f : Nat → Nat` need not preserve the source-tree
   order or consecutive ancestor types. The theorem is an image-set
   consequence only; actual diary geometry must construct a
   strictly increasing, compatible cut map.
3. Without off-image quietness, there may be an extra bad target cut
   completely invisible to the representative. Equal flags at all
   mapped cuts would then be insufficient.
4. If only the ordinary-L graph-age shadows agree, neither terminal
   nor full dependent L+ crossing-failure flags must agree.
5. Matching the marginal old and upper L+ type sets is insufficient;
   each old pair must have a **single** physical witness. The E55
   physical crossing relation already encodes this.
6. Equal Boolean flags do not identify source nodes, multiplicities,
   E/parameter assignments, labelled endpoint preimages or monoid maps.
7. The independent finite source-node index choices from E54 are not
   needed in this new theorem: E55 already removed that dependence.
8. An arbitrary `f` may identify two bad cuts, so equality of
   cardinalities requires additional injectivity; we claim only
   the always-valid upper bound.
9. If the representative top depends on the occurrence rather than
   on the finite diary, the numerical cardinal bound is not uniform.
10. The K4 q2 microevents (source 10 and 22, selected x=38) must
    appear as actual bad/allowed cuts when their complete Kpt
    sources witness that obstruction. Do not delete them.
11. Failure of `NewRootNoNoveltyAtCut` can occur without a newly
    selected cut. The verified sandwich is one-way; bad-cut
    support is not identical to the set of newly interesting levels.
12. A uniform bound on the NUMBER of bad cuts is not a finite
    labelled-envelope carrier or a big Ramsey upper bound without
    the additional complete labelled source/monoid orbit proof.
13. There is no new theorem about exact BRD, and none of the
    manuscript's 12 global pending claims changes status.
14. `oldTop=0`: Bad₁ is empty; off-image quietness is required
    at every old-boring target cut, forcing Bad₂ empty.
15. Source pin/control: formalize this theorem as an independent
    module *importing verified E55*, never copying its four
    failure-flag definitions. Explicitly build the module and
    strictly check each new qualified declaration's axioms.

## Stopping criterion for this stage

Once a complete standalone kernel build and exact-head named-axiom
audit pass, this result is a verified **conditional cut-transport
reduction**. Its proof does not construct a diary-derived f,
nor verify off-image quietness or full labelled-orbit transport.
Those remain the central geometric objectives of Track G.
