# Track A — generation-height bound for physical partial-cut cliques

15 November 2026. English proof and hostile audit committed BEFORE Lean.

## Exact statement

Let k,b,g,M be numerical-H parameters with g<=k and E an
undirected original graph. Let s be a directed clique in the
**actual EVEN old prefix pool** of numbered finite H coordinates
[0,hPosition(k,b,g)). Suppose s contains the actual real copy
v=hPosition(k,b,m) of the CURRENT original b, with m<g.

Then
  |s| <= m+1 <= g.

Crucially, this bound depends on the current b's generation, not
on the number b of earlier originals; it holds even with arbitrary
gaps and additional old selected/parameter original names.

## English proof

Since the current generation m<g<=k, v is not a top-generation
copy. Let t=s\{v}.

Every x in t is a real coordinate iota(i,q) with i<=b and q<=k,
by the exact EVEN partial-prefix decomposition. The positive
actual L atom from x to v excludes i=b: the numerical-H
generator requires two DISTINCT original names, independent
of base graph loop bits. Hence i<b. Because the second original
b has non-top generation m<k, the only possible generation gate
for this positive edge is STRICT q<m: the top-top exceptional
gate is closed. Thus every x in t has generation q in [0,m).

Moreover, distinct x,y in t have DISTINCT generation numbers.
Indeed, if q_x=q_y<k, neither of the two ordered source-label
orientations can satisfy the strict increasing-generation gate,
and the exceptional top-top gate is also closed. The
complete directed clique hypothesis requires the physical L
atom L(x,y)=true, contradiction. This uses the actual generator
in BOTH source index orientations, with original E symmetry
only to flip the L atom when necessary.

Therefore the original numerical-generation decoder restricts
to an injective map t → [0,m). Finite cardinality gives
  |t|<=m.
Since v∈s, |s|=|t|+1 <= m+1 <=g.

The decoder may be chosen noncomputably using the unique
bounded-real representation of each coordinate. Existence
follows from the numericCoordinate_odd_or_real theorem;
uniqueness from hPosition_injective_bounded. It returns the
exact original generation q at iota(i,q) whenever q<=k.

## Adversarial controls

1. b's selected real copy is at m<g<=k, so m<k.
   If m=k the exceptional top-top gate would allow
   earlier old TOP copies with the same generation and the
   bound |s|<=m+1 would generally be false.
2. All s vertices must be in the true EVEN old prefix.
   The theorem is not stated for odd fake coordinates.
3. No original indices are assumed consecutive.
4. The clique is for actual finiteNumericHL binary L,
   not a combinatorial invented edge relation.
5. Source original identities come from the real
   coordinate decoder, and x≠v rules out another
   copy of b by the positive source projection.
6. For earlier i<b adjacent to current b at generation
   m<k, the generation gate forces q<m, not q<=m.
7. Injectivity of generation among x,y distinct also
   uses the top-top gate being closed below k.
8. The chosen current original b need not be the
   only original whose base E bits are positive;
   old graph E arbitrary symmetric.
9. We do not use |P| or cardinality of a clique
   neighbourhood in place of its clique capacity.
10. The bound is valid for m=0: any clique
    containing b generation 0 is a singleton.
11. Height k=0 admits no m<g<=k, hence theorem
    is vacuous, consistent with the empty partial pool.
12. Every physical bounded coordinate must decode
    with generation q<=k, including gap originals.
13. The theorem is **purely a bound** and does not
    construct the staircase witness attaining it.
14. No U-support eligibility is needed once the
    actual clique and its current b copy are given.
15. Nothing here proves a B3 event is boring:
    parameter-closed Kpt E sources remain independent.
16. No infinite resolved-copy schedule, labelled orbit
    or general BRD statement follows.

## Lean acceptance

Implement independently from the full sharp-capacity theorem:
- a generation decoder with exact bounded real-coordinate equation;
- positive physical real-real L below the top requires
  different generation values;
- the finite clique containing current non-top b has
  size at most g, with explicit finite-set injection
  into a generation interval.

This is the key geometric upper estimate for the
remaining sharp formula. Require exact-head direct module
compilation, fully qualified named standard-only axioms,
and full Lake build. Do not turn the global manuscript
upper bound green until all dependent source coherence
theorems are proved.
