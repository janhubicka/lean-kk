# Track F — the actual finite Henson one-type preorder and largeness

15 November 2026. English-first proof and hostile audit; stacked after
`TrackFRealHensonRankDrop.lean`. No published diary lower-bound result is assumed.

## Nodes and extension order

Fix `ell >= 3` and the *actual* graph `E`. A finite one-type node is
a pair `(m,U)` with `U subset [0,m)` and
`finitePoolCliqueCheck E (ell-1) U=false`. The latter is precisely
`cap_E(U)<ell-1`, so this is the true consistency criterion for a new
`K_ell`-free one-point gluing over the old prefix, assuming the old
graph avoids `K_ell`.

Define `(m,U) <= (n,V)` iff `m<=n` and for every `x<m`,
`x in U <-> x in V`. This is a preorder (indeed a partial order up to
proof-irrelevant certificates). It is the actual chronological
neighbourhood-prefix relation, not subset order on arbitrary
non-chronological neighbourhoods.

Define zero-based rank
`rk(m,U) = ell-2-cap_E(U) = (ell-1-cap_E(U))-1`.
Valid nodes have `cap_E(U) <= ell-2`, hence rank is nonnegative.
If `u<=v`, then `U_u subset U_v`: each member of `U_u` occurs below
`m_u`, and the prefix agreement puts it in `U_v`. Actual finite
clique capacity is monotone under inclusion, so `rk(v)<=rk(u)`.

## Rank-preserving zero padding and escape from finite sets

If `n>=m`, the zero-padded node `(n,U)` is valid, extends
`(m,U)`, and has *exactly the same rank*. No graph-realization
hypothesis is needed to define this finite type.

For any finite family `F` of nodes, set
`H = max(m, 1+max{height(z): z in F})`, and take the zero-padding
`v=(H,U)`. Every extension of `v` has height at least `H`,
whereas every member of `F` has smaller height. Hence **the entire
cone above v misses F**. This verifies the precise cone-escape premise
from `RankLargeness.large_difference_of_cone_escape`. Thus *in
this actual type preorder* deleting a finite family from a rank-large
set preserves largeness after a same-rank refinement. This is NOT a
general theorem about arbitrary preorders.

## Real rank-drop extension

Assume the ambient graph has the exact normalized forbidden-family
avoidance predicate and the fixed enumeration satisfies
`OnePointLeftDense`. Fix valid node `u=(m,U)` of zero-based rank
`n+1`. The rank equation and the capacity validity imply
`cap_E(U)+3 <= ell`: this is exactly the rank-at-least-two
condition.

Apply the real graph-specific theorem
`henson_leftDense_exact_type_rank_drop` to obtain a **genuine
original** `v>=m` and new old-neighbour set `U'=U union {v}`
with `cap_E(U')=cap_E(U)+1`, safe
`K_(ell-1)` neighbourhood, and exact old column.

Set the new node `w=(v+1,U')`. It extends `u` because the newly
adjoined neighbour `v` is beyond the old height `m`, and every
old bit remains unchanged. The rank equation gives `rk(w)=n`.
Thus the abstract **rank-drop premise is discharged on actual
Henson one-types**, under explicit graph/fixed-enumeration axioms.

## Consequences

- Apply `RankLargeness.dense_implies_large`: any set of actual
  coding-type nodes dense above an actual node `u` is
  `rk(u)`-large there.
- Apply `RankLargeness.large_difference_of_cone_escape` using the
  zero-padding escape argument: deleting any finite set of actual
  finite one-type nodes preserves largeness on a same-rank subcone.
- These are unconditional *implications under the displayed Henson
  hypotheses*, not a claim that the compatible fibre `A(v)` for
  an arbitrary induced embedding is dense/rank-large. That is
  the next independent geometric step.

## Hostile checks

1. **Prefix equality, not free extension by inclusion:** membership
   outside the old height is unrestricted; below it the edges must
   agree exactly, including nonedges. Otherwise the relation would
   admit non-type extensions.
2. **Rank zero is non-droppable:** the rank-drop theorem is invoked only
   from a node of rank `n+1`, so `cap+3<=ell`.
3. **Finite escape needs a height increase:** merely finding some
   same-rank refinement fails to avoid a finite set containing it.
4. **No hidden tree-wide splitting:** the finite type tree has
   *hypothetical* prefixes; realizing coding vertices uses the separate
   `OnePointLeftDense` theorem. No false claim that every type is
   already a vertex in the prefix.
5. **No `n!` shortcut:** no new BRD count follows from density or
   finite deletion alone.
6. **No lift to multiple types for free:** cone escape and rank drop are
   one-coordinate properties. A tuple of dense fibres can fail to
   realize jointly admissible mixed edges without the richness lemma.
7. **Fixed-enumeration hypothesis is explicit:** `OnePointLeftDense`
   is stronger than merely being `K_ell`-free, and may be stronger
   than the ordinary Henson extension property for an arbitrary
   prescribed enumeration. The manuscript's weaker extension-property
   presentation still needs a separate alignment proof.

## Acceptance

Lean checks must certify the chronological preorder, rank antitonicity,
rank-preserving zero padding, finite-cone escape, genuine one-rank drop,
dense-implies-large and finite-deletion consequences. Record the exact
axiom dependencies. No global diary/degree validation marker is
authorized by this result.
