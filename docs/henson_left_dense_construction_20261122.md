# A nonvacuous left-dense Henson presentation

Date: 2026-11-22. This proof is written before its Lean implementation.

## Purpose and scope

The existing physical constructors assume `OnePointLeftDense E ell`.
The manuscript explicitly chooses a left-dense presentation, but the
existing Lean results do not construct one. Ordinary finite extension
in a given enumeration does not prescribe nonedges to every skipped
index. We therefore construct a presentation with the stronger property
instead of identifying the two properties.

This construction is independent of the proposed nonedge degree. It
proves that the ambient graph assumptions are satisfiable. It does not
prove diary unavoidability, canonization, or the value 24.

## English construction

Fix an integer ell at least 2. Schedule finite subsets of the natural
numbers by

    S_n = decode(unpair(n).first), with an unsuccessful decode giving empty.

Use a fixed encoding of finite subsets. Every finite set S occurs at
arbitrarily large stages: for any lower bound b, stage
`pair(encode(S), b)` is at least b and decodes to S.

Start with the empty graph on the empty prefix. At stage n, inspect the
complete proposed old neighbourhood S_n intersected with [0,n).
If it contains no clique of size ell-1, add vertex n joined to exactly
that set. Otherwise add n with an empty old neighbourhood. Give the new
vertex no loop, add both orientations of every edge, and leave every
old edge unchanged.

Each finite stage is loopless, symmetric, and K_ell-free. The induction
step for clique-freeness uses the exact one-point extension criterion:
a new K_ell would consist of n and an (ell-1)-clique in its complete
old neighbourhood. The empty fallback is safe because ell-1 is positive.

The stages agree on their old prefixes. Define E(x,y) from stage
max(x,y)+1. Coherence implies that E agrees with every stage on its
prefix, hence E is a loopless symmetric K_ell-free graph on Nat.

Now fix a front m and any admissible one-point extension over [0,m).
Let S be its positive neighbourhood, a finite subset of [0,m). Pick
n at least m with S_n = S. The admissibility assumption says that S
contains no (ell-1)-clique in E. By prefix coherence the same holds
at stage n. Consequently the safety test accepts S at stage n, and
the final E-column of vertex n is exactly S on every index below n.
It realizes the requested old column and has no positive edges to
the entire interval [m,n). This is exactly `OnePointLeftDense E ell`.

For ell=4, convert the Boolean table to an ordinary `SimpleGraph Nat`.
The semantic bridge then gives `CliqueFree 4` and the full finite
Henson extension property. In particular, the graph and extension
assumptions in the intended nonedge theorem are not contradictory.

## Adversarial checks before implementation

1. A finite set containing indices beyond n is restricted to old indices
   by the neighbourhood-clique test and the one-point extension formula.
2. No old edge may be changed by a later stage. Global coherence must be
   proved, not inferred from an informal limiting construction.
3. Safety is checked on the entire old neighbourhood, not on individual
   blocks or only selected vertices.
4. The fallback is safe only because ell is at least 2; no empty-clique
   convention is silently used at ell=1.
5. The fair scheduler must be proved cofinal for every finite set, not
   merely surjective once.
6. The realization must be a fresh vertex n at least m. It need not be
   the immediately next original vertex m.
7. Admissibility at front m must be transported through actual equality
   of old edges to the selected later stage n.
8. Every skipped old index lies outside S, so the conclusion gives
   precisely the manuscript's zero tail in both orientations.
9. This produces one chosen presentation. It does not prove that an
   arbitrary enumeration of a Henson graph is itself left-dense.
10. Transfer of a Ramsey theorem to another presentation requires an
    induced isomorphism and invariance of the BRD definition. These are
    separate from existence of the constructed presentation.

## Validation record

The implementation in `Kk/HensonLeftDenseConstruction.lean` has compiled
with the pinned Lean 4.35.0-rc3 toolchain. `edge_cliqueFree`,
`edge_onePointLeftDense`, and `exists_leftDense_cliqueFree` are proved
without graph or density hypotheses beyond `2 <= ell`.

The final focused 52-endpoint transitive axiom audit, including the scheduler,
coherence, clique-freeness, density, and existence endpoints, passed with
only `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom,
`sorryAx`, or native-evaluation axiom occurs in these proof closures.

`Kk/NonedgeBRD24.lean` converts the actual construction to an ordinary
simple graph and proves `constructedHenson4_isHenson4` and `exists_henson4`.
The final nonedge degree remains a separate open goal.
