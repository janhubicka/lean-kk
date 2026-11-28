# Henson universality and model independence: English proof audit

## Intended theorem

Let `G` and `H` be ordinary simple graphs on `Nat`. Assume only that `G`
is `K_4`-free and `H` satisfies the full finite extension property
`Kk.NonedgeBRD.HensonExtension H`. Then there exists an induced graph
embedding `G ↪g H`.

The target does not need a left-dense enumeration. Its ordinary extension
property is sufficient. The source does not need homogeneity, an extension
property, or left-density. No monotonicity of the embedding is asserted.

## Finite extension step

Suppose `p` is an induced embedding of source vertices `[0,n)` into `H`.
Partition its finite image into two sets:

- `U` consists of `p(i)` for `i < n` with `G.Adj n i`;
- `V` consists of `p(i)` for `i < n` with `not G.Adj n i`.

The sets are disjoint because `p` is injective on `[0,n)`. Together they
contain its whole finite image.

The set `U` contains no triangle in `H`. If its vertices `p(i), p(j),
p(k)` formed a triangle, reflection of adjacency by `p` would give a
triangle on `i,j,k` in `G`. Each is adjacent to `n` by the definition of
`U`, so adjoining `n` gives a four-clique in `G`, a contradiction.
This argument checks the complete prescribed neighbour set.

The target extension property therefore supplies a vertex `x` outside
`U union V` adjacent to all of `U` and to none of `V`. Set `p(n)=x` and
leave the previous values unchanged. Freshness makes the extended map
injective; the positive and negative requests give both directions of
the adjacency equivalence for every new pair. Old pairs are unchanged.

## Infinite construction

Start with the empty prefix embedding. Choose one valid extension at
each natural-number stage. The choices can use `Classical.choice`;
there is no additional mathematical existence assumption.

Prove that each step preserves every earlier value and hence that
later prefix embeddings agree on their common old domain. Define
`f(i)` to be the value assigned to `i` at stage `i+1`.

For any two indices `i,j`, inspect one prefix longer than both.
Stabilization identifies its two values with `f(i),f(j)`. Its finite
injectivity proves global injectivity, and its finite induced-embedding
property proves

`H.Adj (f i) (f j) iff G.Adj i j`.

Thus `f` is an ordinary Mathlib induced graph embedding.

## Consequence for big Ramsey degrees

If both `G` and `H` satisfy `IsHenson4`, each is `K_4`-free and each has
the required target extension property. Apply the universality theorem
in both directions. The already proved
`Kk.NonedgeBRD.degreeLE_of_mutual_embeddings` then transfers every
unordered-nonedge degree bound in both directions, and consequently
transfers `DegreeEq`.

This proves independence of the nonedge degree from the choice of
countable Henson presentation. It does not require a full back-and-forth
isomorphism theorem. It does not prove that any numerical degree is 24,
nor does it supply the separate canonization and unavoidability bridges
from a finite diary count to that number.

## Implementation boundary

Planned implementation: `Kk/HensonUniversality.lean`, importing only the
existing semantic module and its dependencies. No new axioms, `sorry`,
left-density assumptions, or enumeration-preservation requirements are
permitted. This English proof is recorded before the Lean implementation.

## Verified implementation outcome

The implementation now compiles with the repository's pinned Lean version.
Both `lake env lean Kk/HensonUniversality.lean` and
`lake build Kk.HensonUniversality` succeeded.

The public endpoints are:

- `Kk.HensonUniversality.inducedEmbedding`;
- `Kk.HensonUniversality.exists_inducedEmbedding`;
- `Kk.HensonUniversality.isHenson4_mutually_embeddable`;
- `Kk.HensonUniversality.degreeLE_iff_of_isHenson4`;
- `Kk.HensonUniversality.degreeEq_iff_of_isHenson4`.

An axiom audit of those five endpoints and the crucial
`PrefixEmbedding.next_vertex` lemma reports only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorryAx` or
project-specific axiom dependency. The full back-and-forth uniqueness
theorem remains outside this file's scope; the claimed degree invariance
is nevertheless completely proved by mutual embeddability.
