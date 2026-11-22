# Nonedge BRD 24: formalization status

## Result

The finite history count **24 is kernel checked**. The ordinary graph and
big Ramsey degree definitions are now connected to the repository's
existing encodings, and the graph assumptions have a constructed model.
**The unconditional nonedge BRD theorem is still not proved.**

This work began from `lean-kk` commit
`a900c510196ce3e1d7551ebb11e2eaaf6da3481a`, with the pinned Lean
`v4.35.0-rc3` toolchain, successor-tree revision
`a74c10761303a18649053f2af3a1a1697f032e13`, and Mathlib revision
`5bd58ac291422a21f412ae354c91e7d172255a2c`.

The manuscript audit uses `kk.tex` blob
`3bc9334ff2f9db1b5f3e36aeb12f1db93e33ff37`. Its direct upper theorem is
stated unconditionally, but the proof of
`lem:small-independent-full-boring` explicitly leaves the needed source
coverage and chosen-type comparison open. The earlier assessment that
only Lean formalization remained was too strong. The independent English
proof also has a gap. This is not a counterexample to the value 24.

## What is proved

| Component | Verified result | Module |
|---|---|---|
| Ordinary graph semantics | The Boolean forbidden family is equivalent to `SimpleGraph.CliqueFree`; loops and both asymmetric orientations are handled correctly. | `NonedgeBRDSemantics` |
| Nonedge copies | Unordered two-element sets, equivalent to images of the genuine empty graph on `Fin 2`; each image has exactly two labelled realizations. | `NonedgeBRDSemantics` |
| BRD quantifiers | Every finite coloring, arbitrary induced self-embedding, all nonedges in its range; equivalent to the usual induced-subgraph formulation. | `NonedgeBRDSemantics` |
| Exactness | A universal upper bound and an unavoidable finite coloring imply the least degree. | `NonedgeBRDSemantics` |
| Model existence | An explicit symmetric loopless clique-free graph on `Nat` satisfies the full zero-tail left-density requirement. | `HensonLeftDenseConstruction` |
| Ordinary Henson property | The explicit graph satisfies `CliqueFree 4` and the full finite positive/negative extension property. | `NonedgeBRD24` |
| Model independence | Any countable K4-free graph embeds inducedly into any target with the ordinary extension property; all `IsHenson4` models have identical nonedge degree predicates. | `HensonUniversality` |
| Finite profile meaning | The capacity triples are in bijection with the existing canonical two-sort integer graph ages; pointwise orders and full Hasse covers agree. | `NonedgeProfileBridge` |
| Exhaustive count | The unbounded accepted-history type is finite with cardinality 24. | `NonedgeHistoryCount` |
| Exact target interface | The two infinite history premises imply degree 24, and it suffices to prove them on the constructed graph. Both premises remain explicit. | `NonedgeBRD24` |

The statements use the copy convention. The two-labeling theorem prevents
confusing unordered copies with embeddings; it does not itself prove a
48-valued embedding BRD theorem.

## The count and its safeguards

The three possible first-split ranks have unique preceding unary descent
chains:

| Split rank | Pair capacities | Complete continuations |
|---|---|---:|
| 3 | `(3,2,3)` | 16 |
| 2 | `(2,2,2)` | 6 |
| 1 | `(1,1,1)` | 2 |

The total is 24. The kernel also checks 13 abstract canonical profiles,
18 full-poset cover edges, and 10 profiles below legal split states.
These are abstract ages; not every abstract profile is a distinct
actual coding-tree front.

The history type is

```lean
abbrev History :=
  {es : List Event // Accepts initialState es}

theorem history_card : Fintype.card History = 24
```

Its definition contains neither 24 nor a fuel bound. Every transition
strictly lowers a proved measure, which gives a length bound. The finite
enumerator is proved equivalent to unbounded acceptance, and every
accepted initial history has exactly one split and two coding events.
Numeric equalities use `by decide`, not native evaluation.

The profile bridge checks all three nonempty supports, empty-support
zero, arbitrary natural-number clique multiplicities, and all possible
generic intermediate canonical ages. Repeated vertices of one sort are
allowed in the multiplicity tests. Left and right coding events remain
distinct even when their successor states coincide.

## What remains unproved

The final target is explicitly recorded as a proposition:

```lean
def NonedgeDegree24Goal : Prop :=
  ∀ G : SimpleGraph Nat, IsHenson4 G → DegreeEq G 24
```

There is no unconditional theorem inhabiting it. To use the checked
conditional criterion, one must construct an actual function

```lean
record : NonedgeCopy constructedHenson4 → NonedgeHistory.History
```

and prove both of these infinite statements:

1. **Upper bound through canonization.** Every finite coloring has an
   induced self-copy on which the color of the image of A depends only
   on `record A`. The image of a function on the 24-element history type
   then contains at most 24 colors.
2. **Lower bound through unavoidability.** For every induced self-embedding
   f and every legal history h, some actual nonedge A satisfies
   `record (NonedgeCopy.map f A) = h`. A bijective numbering of histories
   then gives an unavoidable 24-coloring.

The finite count supplies neither statement. In the independent
manuscript route, the lower construction still needs the complete
chronological two-terminal history/record induction. The upper
construction still needs the full parameter-source comparison and the
corresponding common labelled source orbit. A two-selected-vertex bound
does not bound the number of future vertices in a corrected B3 test:
several future vertices may have the same allowed type.

The detailed current source audit is in
[nonedge_brd_proof_audit_20261122.md](nonedge_brd_proof_audit_20261122.md).
No published exact diary theorem is assumed in the new proofs, and no
frozen manuscript text was edited.

## Reproduction and validation scope

The six new Lean modules are reachable through `Kk.NonedgeBRD24` and the
central `Kk` import. The focused audit uses actual transitive axiom
reports, rather than a source-token search alone:

```sh
lake build Kk.NonedgeBRD24
lake env lean scripts/check_axioms_nonedge_brd.lean > nonedge-axioms.log
python3 scripts/check_axiom_report.py scripts/check_axioms_nonedge_brd.lean nonedge-axioms.log
```

All individual new modules and their principal endpoints have passed
pinned-toolchain compilation and transitive axiom checks. The only
allowed foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, custom mathematical axiom, or native-evaluation
axiom is accepted. The final sequential build of
`Kk.NonedgeBRD24` completed successfully (3,192 build jobs, including
cached dependency jobs), and the aggregate parser accepted **52 exact
transitive-axiom reports**. The structural audit found no suspicious
proof tokens or missing internal imports; all six new modules are in
the central import closure. `git diff --check` passed.

A local full-library build was started and then stopped
because concurrent Lake builds were contending over output artifacts;
no successful local full-library gate is claimed. The focused dependency
closure is checked sequentially.
