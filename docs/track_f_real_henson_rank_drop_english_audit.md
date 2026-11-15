# Track F — real Henson type rank drop from clique certificates

15 November 2026. **English proof and adversarial audit written before Lean.**

This is a genuine graph-specific instantiation, not the rank-drop hypothesis assumed in `RankLargeness.dense_implies_large`. It works in the **unchanged** original graph, uses exact symmetric old columns, and does not postulate diary unavoidability.

## Graph and rank

Let `ell >= 3`. The edge table `E : Nat -> Nat -> Bool` is the actual normalized `K_ell`-free Henson graph, satisfying:
1. the exact forbidden-family avoidance predicate `hensonForbiddenFamily ell`, which implies that every finite old prefix is `K_ell`-free;
2. `OnePointLeftDense E ell`, the fixed-enumeration left-density property: every admissible complete finite neighbourhood column is represented by an actual later original with **zero** bits to all intervening original coordinates.

For a finite set of old neighbours `U subset [0,front)`, let
`a = finiteDirectedCliqueCapacity E U`, the maximum size of a directed clique in `U`. This uses the actual old edge table, not a selected abstract age. The singleton type rank is `r(U)=ell-1-a`. A *valid* new-vertex type has `a < ell-1`.

The theorem assumes `a+3 <= ell`, equivalently `r(U) >= 2`. Its conclusion will construct a genuine original `v >= front` and the extended type `U' = U union {v}` with **exactly**
`finiteDirectedCliqueCapacity E U' = a+1`, and hence `r(U')=r(U)-1`, while still `finiteDirectedCliqueCapacity E U' < ell-1`.

## Real extension construction

Choose, using the finite maximum-clique attainment theorem, a maximal old clique `C subset U` of size exactly `a`. The actual complete neighbourhood of the next original is prescribed to equal the characteristic function of **C alone**, in **both** orientations, with zero bits at every other earlier original (including all unused source parameters and gaps).

Since `a+3<=ell`, the finite set `C` has cardinality strictly below `ell-1`, so it contains no forbidden `K_(ell-1)`. The graph's exact one-point extension criterion and `OnePointLeftDense` therefore yield a **real** `v>=front` satisfying `E(x,v)=E(v,x)=1 iff x in C` for all `x<v`. No new vertex is invented outside the fixed enumeration.

Since `U subset [0,front)` and `v>=front`, `v notin U`. The set of old vertices mutually linked to `v` within `U` is therefore precisely `C`, with no additional links. The already formalized **exact** capacity update says
`cap(U union {v}) = max(cap(U), 1+cap(mutualNeighbours(E,U,v)))`.
The capacity of `C` is exactly `a`: it is at least `a` because `C` is a clique of cardinality `a`, and at most `cap(U)=a` because `C subset U`.
Consequently `cap(U union {v})=max(a,a+1)=a+1`.
Finally `a+1 < ell-1` by the rank-at-least-two hypothesis, so `U union {v}` is still an admissible `K_ell` type.

For **zero padding / cofinal coding witnesses**, start with a valid `U` and any later numerical bound `B`. Apply the same exact one-point theorem to `U` itself at `max(front,B)`, obtaining `v>=B` with `E(x,v)=E(v,x)=1 iff x in U` for all `x<v`. In particular the complete coding column agrees on the old prefix with `U` and is zero on every intervening original.

## Hostile audit — seven concrete traps

1. **No rank-zero drop.** If `r(U)=1` then `a=ell-2` and adding the proposed vertex adjacent to all of a maximal clique would create an illegal `K_ell` with the new future type; the hypothesis `a+3<=ell` is essential.
2. **No cardinality substitution.** `cap(U)` is maximal *clique* size, not `|U|`. Many old neighbours can coexist without a large clique; the construction uses an actual maximal clique `C`.
3. **All actual old indices matter.** Only a complete column zero on `U\C` and on all gaps makes the mutual-neighbour set exactly `C`. An arbitrary positive edge could raise the new capacity further.
4. **Both directions matter.** The directed clique predicate needs `E(x,v)` and `E(v,x)`. The one-point left-density theorem supplies both.
5. **Maximal clique must be attained.** The proof uses the existing finite maximum-clique attainment lemma, not a supremum treated as an unattained infinite bound.
6. **The branch is real but not a global diary.** The theorem constructs one actual coding-type extension; it does **not** prove multi-coordinate class synchronization, homogeneous subcopy rank transport, or one-diary unavoidability.
7. **Left-density remains an explicit hypothesis.** Merely avoiding `K_ell` in an arbitrary graph does not guarantee the prescribed later one-point extension. The theorem never pretends otherwise.

## Formalization acceptance

Prove in a new module the real same-cone cofinal coding extension and the real one-step type rank drop, then expose a `#print axioms` audit for both. Confirm the statements mention actual `hensonForbiddenFamily`, `OnePointLeftDense`, full old columns, and the true finite clique capacity. A successful CI establishes the **one-coordinate** Henson geometry, not rank-largeness of arbitrary fibres or the global lower theorem.

**Next:** build an explicit prefix-node preorder of valid Henson one-types, prove capacity rank is antitone under inclusion of actual old neighbourhoods, and use the one-step real extension to instantiate `RankLargeness.dense_implies_large`. Separately prove rank-preserving zero-padding yields a same-rank cone above a bound, so the conditional finite deletion lemma can be invoked on actual coding nodes.
