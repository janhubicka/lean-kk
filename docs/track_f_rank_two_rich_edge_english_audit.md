# Track F — rank-two richness: every rank-one-large ACTUAL coding set contains an edge

17 November 2026. English proof and hostile audit written BEFORE Lean.
Here rank is ZERO-BASED in Lean: source rank 1 corresponds to
manuscript singleton rank 2. The target is the first genuine
source-clique richness instance, NOT the full induction.

## Statement

Fix any ell>=3 and ACTUAL original-graph edge table E.
Let u be a consistent finite Henson one-type of zero-based
rank 1, and S a set of finite type nodes with:
(1) S is rank-1 Large above u in the already verified recursive
rank-largeness sense, and
(2) every x∈S is an ACTUAL coding node for original vertex x.level,
with the exact complete old adjacency column in both directions.

Then there are actual coding nodes x,y∈S with x.level<y.level,
and E(x.level,y.level)=E(y.level,x.level)=true.

There is no need to assume an independent diary theorem,
Henson OnePointLeftDense, or the global BRD result: existence
of the necessary lower-rank daughters comes directly from
rank largeness. (A set S satisfying this largeness hypothesis
need not exist in every arbitrary graph; the theorem is conditional.)

## Proof

The verified finite-fan lemma gives TWO rank-0 descendants a,b
above u, each carrying rank-0 largeness (= density) of S, with
disjoint fresh positive old-neighbour marker sets:
 A=a.neighbours\u.neighbours,
 B=b.neighbours\u.neighbours,
 and A∩B=∅.

Zero-pad a,b to one height H=max(level(a),level(b)).
Density of S above a lets us choose an ACTUAL coding node
x∈S extending the all-zero padding of a at H.
Thus x.level>=H and its positive old bits below H equal
a.neighbours, so it sees NO marker of B.

Let U=u.neighbours and V=b.neighbours. Since u≤b, U⊆V.
Because rank(u)=1 and V is rank0, the genuine finite clique
capacities satisfy cap_E(U)+3=ell and cap_E(V)+2=ell.
They are exact consequences of the one-type rank definitions
together with their K_(ell-1)-free validity certificates.

Set M = mutualLinkedNeighbours(E,V,x.level), the vertices
of V adjacent to the actual coding original x.level in BOTH
directions. We claim M⊆U. Indeed any c∈M\U belongs
to B, so c<H. Since x is an ACTUAL coding original
and E(c,x.level)=true, its type includes c. As x extends
the zero-padding of a, c∈a.neighbours; together with
c∉U this places c∈A, contradicting A∩B=∅.

The VERIFIED exact clique-capacity insertion recurrence gives
 cap_E(V∪{x.level}) =
   max(cap_E(V), 1+cap_E(M))
 ≤ max(ell-2,1+(ell-3)) = ell-2.
Therefore V∪{x.level} is STILL K_(ell-1)-free and has the
SAME rank 0 as b. Form a legitimate hypothetical type
t=(x.level+1,V∪{x.level}), extending b, by zero padding
all other indices and giving bit one at x.level.

Because S is dense above b, it contains an ACTUAL coding
node y extending t. The bit of y at x.level is then one
in both orientations. Since x.level<t.level≤y.level,
the actual original vertices are distinct and ordered.
Thus S contains a genuine edge.

## Hostile checks

1. Do NOT infer the edge from two merely incomparable cones.
   The crucial step is the exact mixed-neighbourhood capacity
   calculation allowing the second cone to SEE the first
   selected coding original x without losing rank0 density.
2. The selected x must be an ACTUAL coding node, not a
   hypothetical type with an abstract positive bit.
3. Pad BOTH daughter cones to H. Without padding, x might
   be chosen before a second-daughter marker's index,
   so its bit there would not be determined by a's type.
4. Rank definitions are zero-based: the theorem proves the
   manuscript rank-2 (not rank-1 or rank-3) clique witness.
5. The exact capacity of U is ell-3, and of V is ell-2.
   Both require the VALID one-type safety certificate;
   unqualified truncated Nat subtraction can lie.
6. The mutual-neighbour set M uses both edge directions,
   but membership in it implies forward adjacency to x,
   which suffices to force the marker contradiction.
7. An actual coding y realizing t must be later than x.level.
   This follows from t.level=x.level+1, not from any order
   property of an external induced embedding.
8. No symmetry is assumed secretly: both positive directed
   bits are explicit conclusions of IsCodingNode y.
9. This is only ONE-SOURCE rank-2 richness. Rank-3 triangle
   richness and the full finite MULTI-SORT graph-age
   realization remain unverified; neither follows merely
   from this edge witness.

## Acceptance

First formalize a rank0-safe extension which sees the
first actual coding vertex using the verified insertion
capacity recurrence. Then apply density to extract the
second vertex and conclude a genuine edge. Audit exact
statement and standard-only transitive axioms in a
dedicated Lean build. Leave all global BRD and diary
validation marks pending.