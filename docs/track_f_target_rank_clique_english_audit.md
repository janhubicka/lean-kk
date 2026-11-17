# Track F — target singleton-rank lower bound from an actual future clique

17 November 2026. English proof and adversarial audit **before Lean**.
Uses the actual Henson ordinary-graph edge table, maximum old clique
capacity, and full finite-`K_ell` exclusion. It does not assume
diary unavoidability or the lower big Ramsey degree theorem.

## The target rank obstruction

Fix `ell >= 2`, an actual simple symmetric graph edge table `E`,
a finite target old neighbourhood `P subset [0,front)`,
and a finite set `W` of **future original vertices**, each at
index at least `front`. Suppose:
- `W` is a (directed, i.e. both orientations) clique in the ACTUAL graph;
- each `w in W` sees EVERY `p in P` in both directions;
- the complete finite pool `P union W` is `K_ell`-free.

Let `a = finiteDirectedCliqueCapacity E P`. Then
`|W| <= ell-1-a`, i.e.
`|W| <= finiteHensonTypeRank ell E P`.

**Proof.** The genuine maximum old clique capacity `a` is attained
by a finite clique `C subset P` with `|C|=a`. Because
`P subset [0,front)` and `W subset [front,infty)`, the sets
`C,W` are disjoint. By the complete old-to-future adjacency
hypothesis, `C union W` is a directed clique, of cardinality
`a+|W|`. The verified finite clique `K_ell`-free bound says
`a+|W| < ell`, therefore `|W| <= ell-1-a`.
This uses the *actual* full old neighbourhood, not an abstract age
value and not the cardinality of P.

## Henson forbidden-family instantiation

If the target graph `E` satisfies the existing verified
`hensonForbiddenFamily ell` avoidance predicate, then every
finite prefix is `K_ell`-free. The finite set `P union W`
fits in some such prefix, e.g. one more than the maximum
of its original indices. Thus the finite-pool `K_ell`-freeness
assumption above follows automatically, with no new graph axiom.

In an arbitrary induced Henson embedding `e`, if a source
set `X` is a genuine clique and all its images lie after a
fixed target prefix and extend one target type `v`, the image
`e[X]` is a clique in the target type cone. The theorem forces
`|X| <= rank_target(v)`. Hence a separately proved one-sort
source-fibre richness result (presence of a clique of size
`rank_source(u)` in that fibre) implies
`rank_target(v) >= rank_source(u)`.

This is only ONE direction. The reverse inequality
`rank_target(v) <= rank_source(u)` requires transporting
the old clique certificates that bound the source rank.
The mixed multi-sort synchronization remains a further step.

## Hostile checks

1. **An arbitrary future vertex set is insufficient:** W must
   be an actual clique, not just a set of pairwise different
   coding nodes. Finite rank-largeness on its own does not
   create this clique without the richness lemma.
2. **Common old neighbourhood is essential:** every vertex
   of W must see all of P; adjacency to only a subset gives
   no join-clique bound of `a+|W|`.
3. **Both edge directions matter:** the verified directed
   clique predicate cannot silently assume symmetry.
4. **Old/new index separation is explicit:** without it C and
   W could overlap and the cardinality sum would be false.
5. **Old neighbour capacity is not `|P|`:** for a large
   independent old neighbour set, the maximum old clique
   remains one.
6. **The finite graph must be K_ell-free:** the inequality
   fails in a complete `K_ell` graph.
7. **No tacit source embedding:** the base statement refers
   to actual target vertices. The embedding application
   requires a separate image-clique preservation lemma.
8. **Do not infer full compatibility:** this proves only
   target rank >= source rank when a source clique witness
   is separately provided.

## Lean targets

Formalize `targetRank_ge_of_future_clique` from
`finiteDirectedCliqueCapacity_attained`,
`finiteClique_card_lt_of_pool_cliqueFree`, and
`IsDirectedCliqueOn`. Then derive a version assuming
normalized `hensonForbiddenFamily` avoidance in place
of the finite-pool certificate. Audit named axiom reports
at the exact head. Do not add green global diary/BRD marks.