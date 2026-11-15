# Track A — exact clique-capacity projection from complete numerical-H real-generation pools

**15 November 2026. English proof and adversarial audit BEFORE Lean.**

This result supplies the missing bridge between the genuine original-graph
common-neighbourhood capacities used by the now-verified finite positive
cover step (Track A #199) and the real numerical-H L age of *complete*
old-original blocks. The result is about the ordinary binary graph L,
not auxiliary Kpt E or parameter closure.

## Exact numerical rule

At height k, the genuine real numeric coordinate of original i at
generation q is

    iota_k(i,q) = 2*(k+1)*i + 2*q,    0<=q<=k.

The literal H binary relation is generated ONLY from distinct
originals i<j with a generation gate
    q<m OR (q=m=k).
Both ordered L atoms are copied in their matching original tuple
orientation. Odd fake coordinates have no positive binary L atoms.

The defining generator immediately gives, for any two *bounded real*
coordinates x=iota(i,q), y=iota(j,m), the one-way implication

    L^H_k(x,y)=1  implies  i != j AND E(i,j)=1.

**The proof must not silently assume the generation gate is open.**
It extracts the actual HNumericCrossing generator and uses injectivity
of the bounded real encoding to identify both original coordinates.
For the reversed generator orientation, the original base bit
is E(j',i'), which is precisely E(i,j) after endpoint identification.
No symmetry of E is needed for this positive-edge projection.

A corollary is that distinct generations of the SAME original are
never L-adjacent, even if E(i,i) were true: the numerical generator
always uses i<j.

## Full real-copy pool and projection

For any finite original set P define

    Copies_k(P) = {iota_k(i,q) : i in P, 0<=q<=k}.

Every element has a bounded real representation. Choose a total
original-index decoder orig_k(z) that returns the original i on any
bounded real coordinate z=iota(i,q) and an irrelevant default 0
outside the real-coordinate range. This is well-defined because
the already verified hPosition_injective_bounded proves uniqueness
of both original i and generation q.

For a directed L-clique s subset Copies_k(P), the map
z |-> orig_k(z) is injective ON s:
if x != y but orig_k(x)=orig_k(y), the directed clique requires
L(x,y)=1, contradicting the generator projection (which forces
the originals to differ). Consequently

    |s| = |orig_k(s)|.

Every directed pair of distinct elements of orig_k(s) comes from
a distinct pair x,y in s (their images are distinct), and their
positive H edge projects to E(orig(x),orig(y))=1. Therefore
orig_k(s) is a genuine original-graph directed clique inside P.

Thus EVERY numerical-H clique in complete real copies has size
at most cap_E(P). This includes cliques mixing arbitrary
generations, and rules out spurious capacity increases caused
by multiplicity of numerical copies.

## Reverse capacity bound using top generation

The already kernel-checked top-generation theorem establishes
for any distinct original i,j

    L^H_k(iota(i,k), iota(j,k)) = E(i,j)

in BOTH ordered tuple directions, including all missing bits,
provided E is symmetric for the stated two-sided comparison.
Therefore i |-> iota(i,k) is an induced embedding of the finite
original graph on P into Copies_k(P). It is injective on all
original indices.

Hence

    cap_E(P) <= cap_L(Copies_k(P)).

Combined with the projection inequality:

    **cap_L(Copies_k(P)) = cap_E(P).**

For the clean numerical-H theorem we assume E symmetric, as
required by the existing fully induced top transport. The
upper projection itself is stronger and needs no symmetry.

This is equality for the **COMPLETE set of generations** of P.
A partial reserved real-copy prefix need not contain top copies
of every reserved original, so its capacity can be smaller;
the previously verified sharp formula at the pivot remains
`if g<a then a else a+1`.

## Exact typed old-column age transfer

Let c(i,t) be a complete prescribed original-to-future
typed column and U a nonempty admissible sort support.
For each bounded real old copy x, define

    c_real(x,t) = c(orig_k(x),t).

The old real-copy common-neighbourhood of U is exactly

    Copies_k( {i in P : for all t in U, c(i,t)=1} ).

This follows from the exact decoder orig(iota(i,q))=i,
not from any unjustified assumption that the whole original
set P is a clique. The capacity equality above therefore yields

    B_real(U) = ell-1-cap_L(common real-copy U-neighbours)
              = ell-1-cap_E(common original U-neighbours)
              = B_original(U)

**pointwise for ALL admissible nonempty supports U.**

As a consequence, their normalized integer-witness feasible
sets and canonical integer graph-age functions coincide
without any positivity hypothesis.

## Odd fakes and literal full prefixes

Odd dummy positions are NOT part of Copies_k(P), but their ordinary
binary L bits to every selected top original are false; a complete
future typed column must assign every such dummy an all-zero column.
For nonempty support U, no odd dummy can enter a common
future neighbourhood. Therefore adding a pool of dummy vertices
with all-zero future columns cannot change this raw age.

The separately required *literal prefix partition* is:
at a cut after the ENTIRE last top copy of originals i<b, the
numeric range [0,2*(k+1)*b) consists of all bounded real
coordinates of i<b together with all odd dummy coordinates
in the range. No real coordinates outside the block appear.
This geometric partition can be derived from the division
algorithm and the existing `numericCoordinate_odd_or_real`,
but do NOT state the full-prefix identity as verified until
that part is explicitly proved.

In particular a cut INSIDE a block can omit the current
original's top copy; the full-real-copy capacity equality
does NOT apply to the cut's entire real pool.

## Adversarial checks

1. **Multiple generations of one original are not a clique.**
   The generator demands distinct originals, hence the
   projection is injective on any H clique.
2. **All directed arcs:** the projection uses the full
   literal ordered generator, including reversed source arcs.
3. **No fake positive atoms:** odd dummies have none, but
   may carry auxiliary E parameters; do not erase their
   E incidence.
4. **Top gate essential:** an original E edge may disappear
   among two equal non-top generations. The upper capacity
   bound only uses top-to-top copies.
5. **No cardinality shortcut:** cap(P) is a clique capacity,
   not P.card.
6. **No symmetry needed for projection:** it is needed
   for the existing bidirectional top exactness theorem
   and for the Henson application.
7. **Empty P:** both directed clique capacities are 0
   (the empty clique exists); the theorem remains true.
8. **Height k=0:** each original has one real coordinate,
   the top gate applies even at generation 0.
9. **Nonconsecutive original indices:** the pool uses
   actual i in P, no re-enumeration and no new original
   graph.
10. **No outside-carrier confusion:** the Boolean H L table
    is total on Nat. To interpret every copy as an ACTUAL
    finite H vertex, separately choose M exceeding the
    maximum coordinate in Copies_k(P); prove carrier inclusion.
11. **Common-neighbourhood equality on ALL supports:** not
    one selected sort, not merely one positive bit.
12. **No pointwise raw ideal-cover claim:** this theorem
    compares full numerical real-copy old age with the
    ORIGINAL age for the SAME columns; the new isolated
    block age is treated separately by #191.
13. **Partial generation cuts excluded:** equality of
    cap for a complete real-copy set does not automatically
    hold at a partial reserved pivot.
14. **No infinite stage induction:** this is a finite
    exact L capacity and raw-age transport, not existence
    of the coherent resolved diary.
15. **No full L+ source/orbit:** parameter-closed B3,
    auxiliary Kpt E, source labels and BRD
    occurrence factorization are independent.

## Lean acceptance

New independent `Kk/FullRealGenerationCapacity.lean`:
- `numericHCompleteRealPool` and exact membership;
- `numericHRealOriginal` and unique bounded decoding;
- `numericH_real_positive_projects_original` (both generator orientations);
- `finiteNumericH_complete_real_capacity_eq_original`;
- `finiteNumericH_complete_real_common_pool_eq`;
- `finiteNumericH_complete_real_raw_age_eq`;
- canonical and feasible age corollaries;
- optional explicit finite carrier bound.

Run exact-head module build, fully qualified named strict
standard-only axiom audit and full `lake build`.
No changes to `Kk.lean`, `scripts/check_axioms.lean`,
`docs/validation.md`, protected manuscript `kk.tex`
or `validation.tex`. Track G owns integration and markers.
