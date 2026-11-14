# Track A — literal raw age after an isolated support-T reserved block

14 November 2026. English proof and adversarial audit, committed BEFORE Lean.

## Data and target

Let E be a directed Boolean ordinary-L table on the actual original
indices. Fix finite, DISJOINT old P and newly reserved Q, with E(p,q)=false
for EVERY p in P and q in Q. The directed-clique definition checks every
ordered off-diagonal atom, so this one crossing orientation suffices for
the combinatorial bound; Henson symmetry supplies both physical directions.

Let c(p,t) specify the complete typed old-to-future columns and let T
be a designated nonempty admissible support. For q in Q, the block is
connected to precisely the sorts in T. Define the complete augmented
column c_Q(p,t) to equal decide(t in T) when p belongs to Q, and c(p,t)
otherwise. Disjointness preserves c on all p in P.

For every admissible support U, define
  R_P(U) = {p in P : c(p,t)=true for ALL t in U},
  rho_P(U) = finiteDirectedCliqueCapacity(E,R_P(U)),
  qcap = finiteDirectedCliqueCapacity(E,Q).

The exact pointwise formula is:
  R_(P union Q)(U) = R_P(U) union (if U subset T then Q else empty),
  rho_new(U) = if U subset T then max(rho_P(U),qcap) else rho_P(U),
  B_new(U) = ell - 1 - rho_new(U).

All support subsets U are tested, including PROPER sub-supports of T.

## Proof A — isolated union clique capacity is a maximum

For finite X and Y with E(x,y)=false for all x in X,y in Y,
  cap_E(X union Y) = max(cap_E(X), cap_E(Y)).
Take a capacity-attaining clique s inside X union Y. If s is a subset
of neither X nor Y, choose x in s but outside X (thus x is in Y) and
y in s but outside Y (thus y is in X). The two are distinct; s being
a directed clique forces E(y,x)=true, contradicting crossing zeros.
So s lies in one side, giving the upper bound. Each side embeds in
its union, giving the reverse inequalities by capacity monotonicity.
This reasoning even allows X,Y to overlap; only the subsequent
old-column splitting theorem requires the disjoint P,Q.

## Proof B — exact common-neighbourhood set identity

A point p of P union Q belongs to the common neighbourhood for U
exactly if c_Q(p,t)=true for every t in U. If p is in P, disjointness
forces p outside Q, so this is the original old condition p in R_P(U).
If p is in Q, the condition is t in T for every t in U, precisely
U subset T. This proves the displayed literal finite set equality.
When U is not a subset of T, choose t in U outside T: all reserved
vertices fail that bit. The proof does not assume that Q is a clique.

Apply Proof A to R_P(U) and Q when U subset T; otherwise the common
pool equals R_P(U). Taking ell-1 minus capacity gives the raw bound.

For a genuine reserved CLIQUE Q, qcap=Q.card, but this further equality
must be established separately; using cardinality for a general Q is
not valid.

## Necessary counterexample: pointwise age differs from ideal cover raw

Take ell=4 and two sorts x,y. Let P be empty. Let T={x,y}, and
let Q be a genuine 2-clique. Before adding Q, B_P({x})=3.
After adding Q joined to both x and y, B_new({x})=1.
But the ideal rawCliqueBlockBound at T modifies only coordinate T and
leaves the raw {x} value 3. Thus the two RAW functions are NOT
pointwise equal.

Their joint finite clique-feasibility constraints can nevertheless
be equivalent: the single constraint that the clique capacity of
the T-labelled future subpool is at most 1 already enforces every
proper U subset T to have at most 1. That equivalence is established
by the separately kernel-checked finiteClique_full_constraints_raw_block_iff.
Do not substitute a false raw-function identity for it.

## Hostile audit

1. P and Q must be disjoint or the reserved-column if-branch could
   override an existing old p-column.
2. Original E is unchanged, and all original labels are literal.
3. The isolation P-to-Q is essential; mixed clique capacity can
   exceed the maximum if one positive crossing edge appears.
4. Directed cliques test both ordered arcs; a known zero in one
   direction kills mixed cliques. The actual Henson graph is symmetric.
5. Q need not be complete; use exact clique capacity, not cardinality.
6. Full support containment U subset T is essential, not U intersects T.
7. Outside-T typed columns on reserved originals MUST be zero.
8. The update affects proper nonempty U subsets of T and cannot
   generally be modelled by one changed raw coordinate.
9. The integer canonicalizer may preserve the feasible family even
   when pointwise raw ages differ.
10. The raw bound may be zero, and no positivity of a genuine age
    is automatically inferred.
11. A finite block and future are not automatically physically
    realized over any arbitrary fixed past; Henson left-density plus
    complete mixed neighbourhood certificates are separate.
12. The result proves ordinary graph L only, not auxiliary H+ E,
    corrected B3, a common source orbit or any BRD count.
13. For an empty U the set formula is still valid but the integer
    graph-age support subtype excludes it; no empty-coordinate age
    is introduced.
14. A neutral padding interval of originals with zero future columns
    does not change this raw formula on nonempty U; this is handled
    by the independent cofinal-neutral theorem.
15. This is a single finite stage identity, NOT an unbounded
    canonical resolved-copy schedule.

## Formal deliverables

Independent module Kk/IsolatedSupportBlockRawAge.lean:
 - finiteDirectedCliqueCapacity_isolated_union_max;
 - supportBlockOldColumn and exact old/reserved bits;
 - supportBlockCommonNeighbourPool_eq;
 - supportBlockRawBound_exact;
 - supportBlockRawBound_le_old, if useful.

Full strict verification: explicit module build, fully qualified named
standard-only transitive-axiom reports, and full lake build at exact PR head.
No changes to Kk.lean, central validation marks, or frozen manuscript.
