# Track B: canonical ages under arbitrary changes of sorts

## English argument, written before the Lean implementation

Let pi:D'->D be any map between finite sort sets. It may delete sorts,
identify two new sorts with the same parent, or do both. Let B be a raw
bound on the nonempty subsets of D of size at most ell-1, where ell>0.
Assume support monotonicity: B(S)<=B(T) whenever S is contained in T.
Define B'(U)=B(pi[U]). Write G for the canonical bound obtained by taking
the maximum, at each support, over all nonnegative integer multiplicity
vectors of total size at most ell-1 satisfying every raw inequality.

Then

    G_B'(U) = G_B(pi[U])

for every admissible U. Unlike the earlier raw-image identity, this is an
equality of the two genuine canonicalizers in different sort dimensions.
It includes a literal split, where two children have the same parent.

### Pushing a new vector to the old sorts

Given a B'-feasible vector w, put v(t)=sum{w(u):pi(u)=t}. The total mass
is unchanged, so v is a normalized old vector. For any old support S,
let T={u:pi(u) belongs to S and w(u)>0}. The full preimage of S might be
too large to be an admissible support, which is why zero-weight children
must be discarded. Every element of T contributes at least one to the
total mass. Hence |T|<=sum w<=ell-1.

If T is empty, v(S)=0. Otherwise T is an admissible new support and

    v(S)=w(T)<=B(pi[T])<=B(S).

The last inequality is exactly the support-monotonicity hypothesis.
Thus v is old-feasible. Moreover w(U)<=v(pi[U]); children outside U with
the same parents can only add mass on the right. Maximizing proves
G_B'(U)<=G_B(pi[U]). No false equality of these two masses is used.

### Lifting an old vector to the requested new support

Start with any old feasible normalized vector v. Set its weights outside
pi[U] to zero. For each t in pi[U], choose exactly one representative
u_t in U with pi(u_t)=t and transfer the entire weight v(t) to u_t.
Give every other child weight zero. In particular a parent weight is
never duplicated among its children.

The resulting new vector w is normalized, its U-mass is exactly the old
pi[U]-mass, and for every new support V,

    w(V)<=v(pi[V])<=B(pi[V]).

So w is B'-feasible. Applying this construction to each old feasible
vector proves the reverse inequality. This direction does not need
support monotonicity. The same lifting applied to the witness supplied
by each value of a genuine age proves that the image pullback of a
genuine normalized positive integer graph age is again such an age.

## Independent mathematical audit

A second reviewer checked both directions before Lean implementation.
The review confirmed the following necessary details.

1. Images of nonempty admissible supports are admissible, even when pi
   is noninjective; cardinality can decrease.
2. The positive part of a full preimage is used to obtain its size bound.
   The full preimage itself need not be admissible.
3. Pushforward uses sums over fibres, not the weight of an arbitrary
   child and not a coordinatewise copy.
4. The upper-bound mass comparison can be strict when a parent has
   positive children both inside and outside U.
5. The lifting representative must lie in U. An arbitrary global
   section need not preserve the value at the requested U.
6. Old weights outside pi[U] are removed, and each remaining old weight
   is assigned to exactly one child, so normalization is preserved.
7. Every raw support constraint is checked in both directions, including
   constraints involving sorts not in the support being maximized.
8. The empty positive-preimage case has mass zero and does not introduce
   an invalid empty support into the age domain.
9. No positivity or saturation assumption on B is needed for the
   canonicalizer identity. A separate genuine-age corollary preserves
   positivity and witness saturation.
10. Support monotonicity cannot be dropped. With ell=3, D={a,b}, a sole
    new sort mapping to a, and B(a)=B(b)=2, B({a,b})=1, the old canonical
    singleton bound is 1 but the pulled-back canonical bound is 2.
11. This is sort transport for an unchanged raw graph-column system.
    Adding a pivot still requires the full protected-pivot budgets.
12. No auxiliary E, parameter-closed Kpt source, corrected B3, common
    labelled orbit, infinite diary schedule, or BRD claim is inferred.

## Hosted integration verification: 20 November 2026

The full hosted integration gate in [PR #414](https://github.com/janhubicka/lean-kk/pull/414),
[run 44781646067](https://github.com/janhubicka/lean-kk/actions/runs/44781646067),
passed for head `4a275de622617da97a132ab8b8adf17cbb989c7b`. CI actually
checked merge `0792d8f297325eb5c80f807c2010a702789f77ac` over the newer
main `ddf60ae5ddba9fbc846dd3072dabc44fdc829ea5`. The complete
**9,727-job build**, parser self-test, and **955 exact named transitive-axiom
reports** passed, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or custom axiom is accepted; all 23 scoped Track B names occur
in the actual successful audit log.

All five new proof modules are byte-for-byte unchanged from the original
verified head `a433ad84f3881da535ee3e7164ff32e3337d2c3c`, which remains a
valid manuscript proof pin. Its earlier [run 44778772393](https://github.com/janhubicka/lean-kk/actions/runs/44778772393)
(9,709 build jobs and 953 reports) is the **historical proof checkpoint**.
The integration updated the central imports and registry, preserving all
932 names from the newer main and adding exactly the same 23 Track B names
(17 new endpoints and six restored protected-pivot checks). Every main
import and report name is retained in its original order.

The [dated evidence record](audits/2026-11-20-track-b-canonical-splits.json)
preserves the original checkpoint hashes and separately records the successful
integration, its actual CI checkout, and current source hashes. This is
hosted verification: the optional local cold build was stopped after hosted
success, and **no completed local full gate is claimed**. The finite scope
above is unchanged; selected-pivot coding, full Kpt/source synchronization,
the prescribed infinite diary, and global BRD conclusions remain open.
