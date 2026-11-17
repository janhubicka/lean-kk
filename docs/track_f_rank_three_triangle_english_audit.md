# Track F — genuine triangle in every manuscript-rank-three-large coding fibre

17 November 2026. **English proof and hostile audit before Lean.** This is the missing one-source K3 witness for exact target rank comparison at Lean rank2 (manuscript singleton rank3). No diary or big Ramsey theorem is assumed.

## Statement

Fix ell>=4, actual original-graph edge table E, a finite consistent Henson one-type u of ZERO-BASED rank2, and a rank2-large set S of finite types with EVERY member an ACTUAL coding original (exact both-directed old adjacency column). Then S contains three actual coding vertices x<y<z forming a K3, with both graph-edge orientations true for every pair.

Rank arithmetic under the VALID type certificates: cap_E(U)=ell-4, each rank1 daughter has cap ell-3, and each rank0 descendant has cap ell-2, where U=u.neighbours. The capacity is maximum actual directed clique size, never |U|.

## Three daughters and first coding vertex

Apply verified finite-fan theorem to choose THREE rank1-large daughter cones a,b,c over u, pairwise incompatible and with pairwise disjoint fresh positive marker sets (their neighbours minus U). Zero-pad each to a common height H beyond their original levels; each remains rank1 large. Choose a REAL coding x∈S extending the padded a cone. Then x.level>=H, and x sees no fresh marker of b or c (full prefix equality plus disjointness). x sees the original positive U, because it extends a≥u.

## Keep b and c at rank1 after inserting x

For d∈{b,c}, the true mutual old neighbour set of d.neighbours and the actual original x.level is contained in U: any mutually linked marker d.neighbours\U would be adjacent to x, hence would also occur as a positive old bit of the padded a; this violates disjoint fresh marker sets. By monotonicity of clique capacity, cap(mutual)≤cap(U)=ell-4. The VERIFIED exact insertion recurrence gives cap(d.neighbours∪{x.level})≤max(ell-3,1+ell-4)=ell-3. Since the old d.neighbours already has capacity ell-3, equality holds. Thus the genuine hypothetical type d_x=(x.level+1,d.neighbours∪{x.level}) remains rank1 and extends d; it is still rank1-large for S by cone monotonicity.

## First lower c to a dense cone

Use rank1 largeness of S at c_x itself to choose a rank0 descendant c0≥c_x where S is DENSE. c0 may introduce fresh positive markers after x; we do not control them directly.

## Then choose y late enough to avoid c0's added markers

Zero-pad b_x beyond c0.level and choose an ACTUAL coding y∈S from its rank1-large cone, using Large.has_member. Hence y.level> x.level and y sees x. Its complete bit column at every source index smaller than c0.level agrees with b_x: positive old neighbours exactly b.neighbours∪{x.level}; all intervening markers are negative.

The crucial intersection identity is c0.neighbours∩b.neighbours ⊆ U. Indeed b's marker indices all lie before H≤x.level, and c0 extends c_x whose old bits below x.level agree with c; b and c share only root-positive U by pairwise marker disjointness. Thus every member of c0.neighbours adjacent to y belongs to U∪{x.level}. Its maximum clique capacity is at most cap(U∪{x.level})≤cap(U)+1=ell-3.

## Keep c0 at rank0 after inserting y

The exact insertion recurrence gives cap(c0.neighbours∪{y.level})≤max(ell-2,1+ell-3)=ell-2. Therefore t=(y.level+1,c0.neighbours∪{y.level}) is an admissible rank0 extension of c0, still carrying density of S. Its old bits include both x.level and y.level. Density yields a REAL coding z∈S extending t, hence z.level>y.level and z sees both x and y in both orientations. This is a genuine triangle x,y,z inside S.

## Hostile audit / hidden hypotheses

1. This is NOT obtained merely from 3 incomparable daughter cones; positive-edge insertion with exact clique capacity is essential.
2. The chosen x and y are ACTUAL original coding vertices, not arbitrary consistent hypothetical types; otherwise their true edges to other old markers could not be inferred.
3. We must choose all three daughters before x and pad a beyond all daughter levels, so x's old bit to both other daughter marker sets is forced zero.
4. We must lower c_x to a rank0 DENSE cone BEFORE choosing y and then pad b_x beyond c0.level, so y has zero bits to c0's extra markers; choosing y earlier would invalidate the capacity calculation.
5. The intersection c0.neighbours∩b.neighbours⊆U requires the b/c daughter markers to be pairwise disjoint and c0 to extend c_x; it cannot be assumed for arbitrary rank0 descendants.
6. x is included in c0.neighbours because c0 extends c_x, ensuring the final z sees x, independently of whether y sees x.
7. Rank arithmetic uses each type's verified K_(ell-1)-free certificate; truncated natural subtraction without safety can falsify cap equalities.
8. Both orientations of every actual edge are required. The proof uses the complete IsCodingNode columns; symmetry is never silently inferred for arbitrary E.
9. Each extension is chronological. y lies beyond c0.level, so inserting y is not a duplicate old index and t really extends c0.
10. The theorem is ONE-SOURCE triangle richness. It does not prove arbitrary multi-sort finite-graph richness, simultaneous compatible target fibres, or full BRD history persistence.

## Lean plan

First prove a general fresh-marker insertion lemma preserving rank under exact capacity bounds, then formalize the time-ordered x/c0/y/z construction. Audit the exact final theorem and standard-only transitive axioms; no new axioms or diary characterization. The manuscript's global lower and dictionary claims stay pending.