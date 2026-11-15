# Track A — literal staircase lower witness for partial physical clique capacity

15 November 2026. English proof and hostile audit BEFORE Lean.

## Exact conditional statement

Fix a symmetric original E, numerical height k, original b,
partial cut g<=k, finite numerical H carrier bound M, future
top originals j(t)>b and an admissible nonempty support U.
Write
  P_U={i<b : all original E(i,j(t)) bits true for t∈U},
  eligible(U) := all E(b,j(t)) true for t∈U,
  N_U = actual old numbered U-common-neighbourhood at the
        cut hPosition(k,b,g).

Assume b is U-eligible. Suppose there is a natural a with
a<g and an increasing list q(0),...,q(a) of ORIGINAL names,
whose last member is q(a)=b and whose first a names belong
to P_U. Assume these a+1 originals form a genuine clique
in E (all ordered pairs E(q(i),q(j))=true for i<j).

Then the ACTUAL physical old U-neighbourhood contains an
L-clique of size a+1, and hence
  a+1 <= cap_L(N_U).

This theorem is conditional on an original clique of the
specified length. It does not yet prove that the full maximum
clique in S_U can be truncated into such a sequence:
the natural ordered-subclique extraction is a separate step
needed to obtain the unconditional sharp lower equality.

## Proof by existing verified numerical-H staircase theorem

Consider the finite ordered reserved-prefix pool
   R = orderedReservedNumericPrefix(k,q,a,a).
By definition it consists of all generations 0,...,k
of the earlier a originals, and generations 0,...,a
of current original q(a)=b. Because a<g<=k,
every coordinate of R lies BEFORE the old numeric cut
hPosition(k,b,g).

The exact actual common-neighbour pool equality from
PR #224 says
   N_U = Copies_k(P_U) ∪ {iota(b,m):m<g}
when b is U-eligible.

Each coordinate of R with index i<a belongs to Copies_k(P_U),
because q(i)∈P_U and its generation <=k. Each coordinate
with index i=a belongs to the second set, because
q(a)=b and its generation <=a<g. Therefore R⊆N_U
as literal sets of numbered H vertices, without
discarding gaps or odd dummy vertices from the source.

The existing independently verified theorem
finiteNumericH_ordered_reserved_prefix_capacity computes
the TRUE numerical-H directed clique capacity of R,
for strictly ordered, possibly nonconsecutive original
names forming a complete original E clique.
Here its parameters are r=a+1, last index a, and
last included generation a. Its exact formula gives
  cap_L(R) = if a<a then a else a+1 = a+1.
The theorem already constructs a staircase clique witness,
so no implicit existence assumption is being introduced.

Capacity monotonicity for R⊆N_U gives
  a+1 = cap_L(R) <= cap_L(N_U).

## Adversarial controls

1. The current original b is U-eligible; otherwise its
   numerical copies do not lie in the common-neighbour pool.
2. The input earlier originals q(i) are ACTUAL elements of P_U,
   not merely abstract labelled vertices.
3. The q sequence is strictly increasing, including its
   final name q(a)=b. It may skip arbitrary ambient originals.
4. The original E pairwise edges form a genuine complete clique;
   no cardinal-only estimate is used.
5. The selected generation of b is exactly a, with a<g<=k,
   so the current top is never accidentally included.
6. The reserved-prefix theorem is invoked with r=a+1<=k+1;
   the necessary arity/height condition follows from a<g<=k.
7. The physical reserved prefix contains *all* generations
   of the earlier q names, not just their designated staircase
   generation; this is harmless because R is a SUBSET of N_U.
8. Odd fake coordinates are in the ambient prefix but
   cannot join N_U for U nonempty; they are not deleted
   from the literal H structure.
9. A=0 produces a one-point clique {iota(b,0)} if g>0,
   as it should.
10. Original E symmetry is used by the existing physical
    reserved-prefix capacity theorem.
11. The statement remains about total Boolean L on Nat;
    carrier membership needs cutoff bounds if claiming a
    finite-H substructure. No such membership is silently inferred.
12. The proof does not assert every lower bound is obtained
    by the same original choice of q across different H
    occurrences or parameter closures.
13. A raw age equality must still account for the other
    clique case, avoiding b, and the original capacity
    cap_E(P_U).
14. No completed-block shortcut at an intermediate cut is used.
15. Full Kpt E/parameter-closed B3 and global diary-labelled
    source orbit remain independent and unproved here.

## Remaining unconditional step

Given cap_E(S_U)=c, choose an original clique of size
a=min(c,g-1) and enumerate its vertices increasingly.
Appending b gives the needed q(0),...,q(a) with all
original E edges. Its existence follows by capacity
attainment, finite-subclique selection and sorted
enumeration; this must be formalized explicitly rather
than embedded as an assumption in a sharp equality theorem.

## Acceptance

Implement Kk/PartialNumericStaircaseLower.lean, using
the actual physical common-pool theorem,
finiteNumericH_ordered_reserved_prefix_capacity and
finiteDirectedCliqueCapacity_mono. Print its qualified
axioms. Require exact-head direct build and full Lake
on a stacked draft branch; no green manuscript equality
mark until the unconditional ordered-clique extraction
also passes.
