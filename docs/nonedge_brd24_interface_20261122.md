# Exact nonedge BRD 24: the remaining typed interfaces

Date: 2026-11-22. English proof and independent adversarial review precede
the implementation in `Kk/NonedgeBRD24.lean`.

## Concrete graph and correct theorem target

Convert the actual Boolean graph `LeftDenseConstruction.edge 4` into
an ordinary `SimpleGraph Nat`. Its finite-prefix clique-freeness rules
out every four-element clique: choose a prefix containing the alleged
clique and apply the proved prefix theorem. Its constructed left-density
implies the ordinary Henson finite extension property through
`hensonExtension_of_onePointLeftDense`.

Thus a graph satisfying `IsHenson4` exists. This is an actual existence
theorem, with no hidden graph, density, or Ramsey hypotheses.

The requested final proposition is

    forall G : SimpleGraph Nat, IsHenson4 G -> DegreeEq G 24.

It will be recorded as an open goal, not declared as a proved theorem.

The separate ordinary-extension universality construction proves that
all graphs satisfying `IsHenson4` mutually embed. Its BRD transport
theorem therefore makes this universal goal equivalent to the exact
degree assertion for `constructedHenson4`. The forward implication
specializes the goal to that constructed model; the reverse implication
transports the degree to any other model. Consequently it is enough to
establish the two history interfaces below for that concrete graph.
This reduction does not prove either interface.

## The finite carrier

Use `NonedgeHistory.History`, the subtype of complete legal event lists
accepted from the initial rank-three state. Its definition contains no
fuel and no occurrence of the proposed answer 24. The complete finite
enumerator supplies its `Fintype` instance and proves cardinality 24.

This is still a finite combinatorial object. Its definition does not
provide a record function on actual nonedges of the Henson graph.

## Sufficient interfaces and their proof

Suppose an actual function `record : NonedgeCopy G -> History` is given.
The two required infinite assertions are the following.

**Canonization.** For every finite coloring c of all nonedge copies,
there exist an induced self-embedding f and a function d on History
such that, for every nonedge A,

    c(map f A) = d(record A).

The history in this definition is the record of the preimage A. No
order-preserving condition is imposed on f. The colors on the selected
self-copy belong to the image of d, which has at most 24 members. The
semantic range-equivalence theorem ensures this includes every nonedge
inside that copy. Consequently `DegreeLE G 24` holds.

**Occurrence in every copy.** For every induced self-embedding f and
every legal history h, there exists a nonedge A with

    record(map f A) = h.

Compose record with a bijection between History and Fin 24. The last
condition says precisely that this finite coloring is unavoidable in
every induced self-copy. Therefore every Ramsey bound is at least 24.
Combining both conclusions with the separately verified exactness
criterion yields `DegreeEq G 24`.

## Adversarial review

The independent review verified these distinctions before Lean coding:

- Canonization must cover all finite colorings, not only the record
  coloring. The palette may identify histories, so it gives an upper
  bound, not an assertion that every coloring uses 24 colors.
- The lower premise is `record(map f A)=h`. Merely having every history
  somewhere in G does not establish occurrence in each induced copy.
- An actual induced graph embedding is needed. Graph homomorphisms can
  turn a nonedge into an edge, and increasing maps are too restrictive
  for the ordinary BRD quantifiers.
- The finite carrier must be the independently specified legal-history
  type, not `Fin 24` introduced as its definition.
- Constructing a Henson model does not construct a valid record function
  or prove either infinite interface.
- This conditional criterion does not discharge the manuscript's
  full-source comparison or the lower-bound history induction. Neither
  premise is promoted to an invariant or supplied by an axiom.

## Status

`lake build Kk.NonedgeBRD24` passed with the pinned Lean 4.35.0-rc3
toolchain. The focused transitive axiom audit passed for 35 endpoints,
including the ordinary graph model and conditional exactness theorem,
using only `propext`, `Classical.choice`, and `Quot.sound`.

The implementation uses the unbounded predicate subtype
`NonedgeHistory.History`, whose proved cardinality is 24. It supplies
`constructedHenson4_isHenson4`, `exists_henson4`, and
`degree24_of_history_interfaces`. The last theorem retains its two
explicit infinite premises. `NonedgeDegree24Goal` is only a proposition
definition; no unconditional proof of it is claimed.

Reproduce the focused check with:

```sh
lake build Kk.NonedgeBRD24
lake env lean scripts/check_axioms_nonedge_brd.lean > nonedge-axioms.log
python3 scripts/check_axiom_report.py scripts/check_axioms_nonedge_brd.lean nonedge-axioms.log
```
