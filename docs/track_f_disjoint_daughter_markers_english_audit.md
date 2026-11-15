# Track F — disjoint daughter-marker sets preserve every mixed raw age

15 November 2026. **English proof and hostile counterexample written before Lean.** This note is stacked on the exact common-neighbour definition from Track F PR #229; it does not assume the published diary degree characterization.

## Statement

Fix the ACTUAL graph edge table `E`, a common old prefix of length `m`, and a later finite length `N>=m`. For each sort `i in Fin d` choose an actual old-neighbour set `U_i subset [0,m)` and a finite set `V_i subset [m,N)` of new positive neighbour coordinates, with all `V_i` pairwise disjoint. Put `W_i=U_i union V_i`.

For every support `S` containing **at least two distinct sort indices**, the exact common-neighbour pools agree:

`{x<N : forall i in S, x in W_i} = {x<m : forall i in S, x in U_i}`.

Proof: take `x` on the left and choose distinct `i,j in S`. If `x>=m`, old `U_i,U_j` cannot contain `x`, so `x in V_i intersect V_j`, contradicting pairwise disjointness. Thus `x<m`. Since each `V_k` has no member below `m`, every membership `x in W_k` for `k in S` reduces to `x in U_k`. Conversely each old common neighbour belongs to each enlarged set and remains below `N`. Equality follows.

Applying the actual maximum directed-clique capacity yields equality of every raw old-clique age bound on supports with at least two different sorts. This conclusion holds for all finite support sizes, including triple supports: there are **no hidden mixed old-clique restrictions** created by disjoint daughter markers.

For singleton `S={i}` the pool is instead `U_i union V_i`; its clique capacity may grow. In the richness induction, choose each newly created daughter cone of rank exactly `s-1`, so the additional singleton bound is exactly `s-1`. The resulting *canonical* mixed ages may nevertheless decrease as logical consequences of these individual singleton constraints. A refinement of an admissible finite graph assigning **at most one vertex to each new daughter sort** preserves all such singleton bounds; its original collapsed graph satisfies every unchanged mixed raw inequality. This is precisely the finite graph-combinatorial part required by the induction. The existence of simultaneously rank-large daughter cones remains a separate geometric proof obligation.

## Necessity and hostile checks

1. **Disjointness is necessary.** For two sorts with empty old neighbourhoods, let `V_0=V_1={v}` with one fresh original. Their common pool gains `v`. In `K_4`, the raw mixed bound decreases from 3 to 2. One cannot replace pairwise disjointness by the weaker condition that each daughter separately lowers its rank.
2. **Freshness is necessary.** If a new marker `V_i` already lies below `m`, it can change old common pools in mixed supports even when marker sets are pairwise disjoint.
3. **Nonempty multi-index support is essential.** The empty-support convention is the whole old prefix and grows with `N`; singleton support can grow as intended.
4. **Repeated labels differ from repeated sorts.** Multiple future vertices may carry one sort label; multiplicity vectors account for this. The pool equality concerns distinct indices of the refined front, not distinct vertices of a clique.
5. **Directed capacity is computed only after the pool equality.** The argument does not assume graph symmetry or any relative Henson embedding; therefore the resulting raw equality is valid for every actual edge table `E`.
6. **No false canonical invariance.** Actual raw bounds on mixed supports remain equal while the canonicalized age may change when a singleton bound becomes tighter.
7. **No global Ramsey conclusion.** Rank-largeness and simultaneous compatible refinement still require distinct geometric/induction theorems. This lemma verifies the fresh-support isolation needed to make those statements mathematically meaningful.

## Formalization plan

Use `trackFCommonNeighbourPool` from PR #229. Define `trackFAddDisjointMarkerSets U V i = U_i union V_i`. Prove old/fresh prefix membership, the exact mixed-support equality under two distinct indices and pairwise disjointness, and the resulting raw-capacity equality. Then prove an explicit counterexample to the disjointness-free assertion in a small Boolean K4 edge table (finite regression acceptable in addition to the proof).

Do not modify any frozen black text or promote manuscript global validation marks. The theorem can support the olive richness proof but does not prove its induction or the resulting lower big Ramsey degrees.
