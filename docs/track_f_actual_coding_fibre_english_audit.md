# Track F — actual coding nodes, root largeness, target-prefix colouring

17 November 2026. **English proof / hostile audit before Lean**.
The previous HensonOneType modules treat ALL finite hypothetical
one-point types as nodes. The lower-bound proof, however, uses the
**coding nodes of actual original vertices** and their target
images under an arbitrary induced embedding. This note makes the
distinction explicit and supplies a certified base case.

## Real coding-node predicate

For an actual finite Henson one-type node u=(m,U), declare that
u is a coding node iff the ACTUAL original vertex m has exactly
old neighbours U:
for every x<m,
 E(x,m) = 1 iff x∈U and E(m,x) = 1 iff x∈U.
The two orientations are included because the Lean graph predicate
does not silently assume symmetry.

A hypothetical type node need not satisfy this predicate.

## Actual coding nodes are dense (under the fixed enumeration axiom)

Let ell>=3 and assume the target/source actual edge table avoids
the verified normalized Henson forbidden family and satisfies the
explicit `OnePointLeftDense` condition.

Given any consistent finite type v=(front,U), its genuine old
neighbour set U has no K_(ell-1) clique. The verified exact
one-point Henson realization theorem produces a REAL later
original x>=front whose complete old column is U on every
index y<x and whose intervening gap bits are zero.
Construct a type w=(x,U), with old support U and safe original
one-point clique-capacity certificate. Then w extends v
without changing any old positive or negative bit, and w is
an actual coding node by the complete-column theorem.

This is exactly density:
for EVERY finite extension v of an initial u, there is
an actual coding node w>=v. By the already verified actual
one-type rank-drop theorem, density implies recursive
rank-largeness at rank(u). Thus the set of REAL coding nodes
is rank(u)-large above each consistent type u.
This does NOT mean every arbitrary subset of coding nodes
(for example a selected target fibre) is large.

## Roots and the initial compatible pair

The unique empty-prefix type root is (level=0, U=empty);
its actual old-neighbour clique capacity is zero and its
zero-based rank is ell-2 (manuscript rank ell-1).

For any map e:Nat→Nat and any second target edge table,
the fibre of the target root includes precisely all
source coding nodes: the prefix length is zero, so
the target bit condition is empty and e(x)>=0 automatically.
No assumption on e is needed for this trivial root case;
for later target levels the induced-embedding property is
essential. In particular, for the source and target copies of
one K_ell-free Henson graph, the root-root pair begins with
matching singleton ranks and a rank-large source coding fibre.

## Finite target-prefix colouring

Given an arbitrary map e:Nat→Nat and a target graph edge table
Etgt, the ACTUAL target bit-vector of a source coding node u
at finite target prefix H is the ordered pair of maps
(`i↦Etgt(i,e(u.level))`, `i↦Etgt(e(u.level),i)`),
for i∈Fin H. The colour type
`(Fin H→Bool) × (Fin H→Bool)` is finite.

Restrict to source coding nodes with e(u.level)>=H.
The old source vertices with images below H form a FINITE set
if e is injective. After deleting those finitely many source
coding nodes, the verified finite-colour rank-large fan theorem
can be invoked on this precise colouring. But the chosen
target-prefix colour's singleton graph rank still needs
a separate richness-to-clique argument; finite colouring
alone cannot establish it.

## Hostile checks

1. The actual coding-node predicate is NOT true for every
   consistent hypothetical one-type. Replacing its set by
   the full type tree would trivialize the density statement.
2. The node's level m is the candidate coding original m;
   old neighbourhood U must lie strictly below m.
3. The complete-column theorem must specify BOTH directed
   orientations, including all intervening gap bits.
4. The source density proof uses explicit OnePointLeftDense,
   which is stronger than merely K_ell-freeness of an arbitrary
   graph. This should not be silently added to the manuscript.
5. Root compatibility is a special case because target-prefix
   length is zero; it does NOT prove every later target fibre
   is rank-large.
6. For finite target height H the colour palette is finite;
   the full infinite target type need not have finite palette.
7. Finite deletion of image indices requires injectivity of e:
   infinitely many source vertices could map into a finite
   target prefix under an arbitrary noninjective map.
8. No root-to-target rank matching for later nonzero target
   prefixes is asserted. That is the pending part of Track F.
9. Canonical multi-sort graph ages and exact diary BRDs are not
   even mentioned in the theorem premises.

## Lean acceptance

Define the actual coding-node predicate, prove its density and
recursive rank-largeness from existing real Henson one-point
realization, formalize the empty-prefix root and its rank,
and define a genuine finite target-prefix colour function.
Prove the target-root fibre is exactly the actual source
coding-node set. Run a dedicated exact-head build and strict
transitive-axiom audit. Do not promote the full richness,
source-target transport, or independent BRD degree marks.