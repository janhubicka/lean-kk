# Actual live-future normalization and coding, 26 November 2026

English proof and adversarial checks before the proposed Lean batch.

## Actual age, not an assumed universal continuation

Fix a finite old vertex set P and an arbitrary (possibly infinite) set W
disjoint from P in an ordinary graph E. A finite sort map s labels W;
every active sort is nonempty. Every finite clique in P union W has size
less than ell. Define A(T) as the maximum of the number of T-labelled
vertices in a finite clique of W. To avoid a maximum over an infinite
set, take the finite set of normalized integer vectors realized by such
cliques. The empty clique realizes the zero vector. A singleton in any
sort in nonempty T gives positivity; normalized vectors bound A(T) by
ell-1. A vector attaining A(T) respects every A(U). Hence A is a genuine
integer graph age, including the vacuous zero-sort case.

For any actual old-to-W columns c, all actual clique vectors satisfy
the raw common-old-neighbour bound: join the relevant part of the
future clique to an old maximum common-neighbour clique. Existing
finiteOldFuture_free_implies_raw_support proves this with both directions.
Thus A <= G_raw. This proof never asserts that the actual W realizes
every graph or every vector permitted by G_raw.

A support maximum can be witnessed by a clique supported entirely on
that support: take the corresponding part of an attaining clique.
On restriction to a set of surviving sorts indexed injectively by pi,
the same witness on the image support lies wholly in the surviving
union. Conversely every surviving clique is an original clique.
Consequently A pulls back along the actual survivor reindexing.

## Actual normalization with fresh auxiliary names

Keep W and its labels fixed. For each genuine cover lower <. upper in
the interval from G_raw to A, choose the unique inclusion-minimal changed
support T (existing theorem), with upper(T)=lower(T)+1. Take r=ell-1-
lower(T) fresh names Q, disjoint from P and W, with cardinal r.
Define E' to agree with E off Q, to be the loopless complete graph on Q,
and to have a positive Q-to-outside bit exactly to vertices in W with
sort in T, symmetrically. This is an explicit graph, not an existence
assumption about a fixed Henson enumeration. Old P and W are unchanged.

Every clique in (P union Q) union W either avoids Q, in which case old
freeness applies, or meets Q. In the second case every outside member
is in W and in T, because Q has no links to old P. The outside clique
size is at most A(T) <= lower(T); inside Q the size is at most r. Hence
the total is at most ell-1. This proves the full relative graph safety
invariant on arbitrary finite subsets, even though W is infinite.
The actual future A is unchanged. Literal old graph and old column
preservation, together with isolatedSupportCanonicalAge_cover_step,
give exact new canonical age lower; at intermediate block sizes the
same theorem gives upper. The physical block is distinct from a
hypothetical single-coordinate raw clipping (the latter agrees only
after canonicalization).

Iterate along the existing finite saturated chain from G_raw down to A.
The genuine-age property of G_raw follows because it lies above A.
Each step has a fresh set from the spare pool; no new future graph is
constructed. Store the actual Q and support T in a path of cover
insertions. The terminal state's age is its actual future age and its
finite old pool extends the initial pool. Finite paths can later be
enumerated block by block with dummy separation.

## Coding and class invariant

With normalized pre-age A, isolate the coding vertex r as a singleton
class and ensure each other class has constant adjacency to r. Restrict
the full equality G_raw=A to the survivors. This uses canonical
arbitrary-sort pullback, not equality of raw bounds on different
domains. Move r from W to P, retaining literal graph edges. Survivor
canonical age is antitone under enlargement of P; the unchanged actual
survivor clique witnesses still give the opposite lower bound.
Consequently the survivor age is unchanged. No controlled-pre-age
algebra is needed for this equality. The stronger full pre-code
formula, used to identify legal zero-code records, still follows by
partitioning actual cliques according to whether they contain r.

For the finite class refinement, complete old-column equality is an
equivalence. A split replaces the class label by (old class,new bit)
on its occupied range. The new equivalence is exactly equality of all
old columns plus the new bit. A constant new bit on each class
preserves equality and separation. Restriction after coding preserves
the same equivalence on survivors. This permits the actual partitions
to use their finite occupied ranges; empty classes are never active.

## Hostile checks and boundaries

* Empty W/d=0: no nonempty support; zero vector still exists for ell>0.
* Nonempty sorts necessary for positivity. Do not force a fictitious
  witness if a sort is empty.
* The cap graph may have unused names; only the actual live union is
  required to be clique-free at intermediate stages.
* Every Q is disjoint from P AND W. Without this, insertion could
  change the original V or old columns.
* Complete two-direction old/future columns are essential.
* Actual future maximum is attained on a support, not a claim of
  universal realization.
* Covers must be genuine; direct normalization by all support bounds
  could skip intermediate histories.
* Distinct old and new blocks are nonadjacent, including to previously
  coded V vertices.
* When using survivor saturation, the original support must omit
  the singleton coded class. Simply deleting a point within a
  non-singleton active class can decrease actual capacity.
* Neutrality is of full canonical ages, not just singleton sizes.
* New proof code will be submitted in a single large batch. The
  kernel/axiom checks are pending until hosted CI actually runs.
* Infinite fair enumeration, ordered retained record parser, actual
  arbitrary-history occurrence and final degree statements are not
  implied by the finite normalization alone.

