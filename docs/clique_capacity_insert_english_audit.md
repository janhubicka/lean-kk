# English-first proof and adversarial audit: incremental linked clique capacity

**4 November 2026 — protocol:** Commit this English proof and hostile audit before the Lean implementation. This is an incremental finite-original-graph lemma, not a claim about the full numerical-H parameter-closed B3 relation.

## Theorem: exact one-vertex update of directed clique capacity

Let `E : Nat → Nat → Bool` be any Boolean directed old-original graph, `L` a finite set of original indices, and `v ∉ L` a new unreserved original.

Let `cap_E(P)` be the largest cardinality of a **directed** clique in the finite induced graph on `P` (defined in PR #54 by a finite powerset supremum, including the empty clique).

Define the **mutually compatible old linked set**

`M_E(L,v) = {x ∈ L : E(x,v)=true AND E(v,x)=true}.`

Then the precise recurrence is

`cap_E(insert v L) = max(cap_E(L), 1 + cap_E(M_E(L,v))).`

This theorem is valid without symmetry, loop-freeness, K_ell-freeness, Henson left density, or a reserved-block label. In the Henson application the actual graph is symmetric, but proving the directed version avoids a hidden graph-language assumption.

### English proof

Any directed clique `C ⊆ L ∪ {v}` either omits `v`, in which case `|C|≤cap_E(L)`, or contains `v`. In the second case the remaining vertices `C-{v}` form a directed clique in `M_E(L,v)`: every remaining `x` is adjacent to `v` in **both** directions. Therefore `|C| = 1+|C-{v}| ≤ 1+cap_E(M_E(L,v))`. Taking the largest size over all candidate cliques establishes the upper bound.

Conversely every clique in `L` is a clique in `L∪{v}`, giving `cap_E(L)≤cap_E(L∪{v})`. Every directed clique `D⊆M_E(L,v)` is disjoint from `{v}` (since `v∉L`) and `D∪{v}` is a directed clique: its new edges are exactly the two directed compatibility conditions. Hence `1+cap_E(M_E(L,v))≤cap_E(L∪{v})`. The two lower bounds give equality.

### Consequences for a fixed live reserved set R

For a new unreserved original `v`, suppose the linked-unreserved pool changes **exactly** from `L` to `L∪{v}`; in particular the set `R` of live reserved neighbours of the next proposed selected original remains unchanged. Then the updated **sufficient** PR #54 budget is

`|R| + max(cap_E(L), 1+cap_E(M_E(L,v))) < q`,

where `q=ell-1` in the big Ramsey application. This checks the new pool `R ∪ L ∪ {v}` by the already verified generic linked-capacity lemma, without inspecting all q-element subsets of that pool.

If `M_E(L,v)=∅` and `cap_E(L)≥1`, then `cap_E(L∪{v})=cap_E(L)`: arbitrarily many **pairwise incompatible** linked unreserved vertices can be added with no extra capacity cost after the first. This is useful for a recursive budget invariant, unlike a crude +1-per-vertex bound.

## Independent K4 regression

Take old linked selected originals `L={1,2}`, with no edge between them, so `cap(L)=1`. Add a new original `v=3` whose edges to `1,2` are both absent. Then `M(L,3)=∅`, the new capacity is still one, and a single live reserved neighbour `R={0}` gives `|R|+cap(L∪{3})=2<3`.

Change the graph so that `1` and `3` are mutually adjacent, with `2` isolated from both. Then `M(L,3)={1}`, the new capacity is two, and the budget for `K_4` reaches three. If reserved `0` sees each of `1,2,3`, a proposed future selected vertex adjacent to all four would produce a forbidden `K_4` through `0,1,3`.

The regression is checked on actual Boolean original edge tables, not abstract diary code.

## Adversarial review

1. **v must be fresh to L.** Without `v∉L`, the claimed equality with the extra `+1` can duplicate an already counted vertex, especially in directed loop-bearing tables. Keep this as an explicit hypothesis.
2. **Both orientations are required.** Testing only `E(x,v)` but not `E(v,x)` is invalid for the general directed encoding. The genuine Henson graph is symmetric, but symmetry should not be secretly used by the generic lemma.
3. **Empty old pool.** `cap_E(∅)=0` and `M_E(∅,v)=∅`, so the formula gives `cap_E({v})=1`. The claimed zero-cost consequence requires `cap_E(L)≥1`, not simply `M_E(L,v)=∅`.
4. **This updates a fixed L and R.** In the *next* proposed selected column, the **live reserved set** `R_b` may differ because the next selected original may choose different passing bits to the reserved block. The identity for `L∪{v}` does NOT automatically describe `linkedUnreserved` for that changed column.
5. **Old/new gap indices.** A selected original may appear after several skipped Henson indices. Each newly selected gap original that is a future positive neighbour may alter the linked set. The recurrence must be iterated over the actual listed additions, not assumed to apply to an interval with ignored positive gap vertices.
6. **Do not equate capacity safety with full B3.** These are ordinary original-edge clique capacities; the full corrected-B3 continuation may include future-to-future edges not equal to original-to-original edges. The real numerical-H K4 cuts 10/22 counterexample remains untouched.
7. **The bound is exact for capacity, NOT for the PR #54 budget.** PR #54's sum `|R|+cap_E(L)` may overestimate the maximum actual mixed clique because a maximal clique in `L` need not be adjacent to all reserved members of `R`. The sufficient budget remains non-necessary.
8. **No global diary claim.** The canonical resolved-copy construction must still prove its per-stage old selected/parameter adjacencies, exact live block tags, complete old neighbourhood tests and assigned full source types. No iteration of this finite lemma supplies them for free.

## Lean deliverables

- Define `mutualLinkedNeighbours E L v := L.filter (fun x => E x v = true ∧ E v x = true)`.
- Prove `finiteDirectedCliqueCapacity_mono`, the two-sided insertion lemma and the **exact** formula for `v∉L`.
- Derive a safe updated mixed pool certificate under the displayed budget and the zero-growth corollary when `M_E(L,v)=∅` and `cap_E(L)≥1`.
- Add the independent safe/unsafe K4 numeric regressions as executable theorem endpoints.
- Append named transitive-axiom checks; require the full `lake build` and strict standard-only axiom audit.
- Edit olive successor manuscript prose and the audit/validation notes; keep protected black statements untouched. The global application remains blue until its hypotheses are verified for the prescribed unbounded schedule.

