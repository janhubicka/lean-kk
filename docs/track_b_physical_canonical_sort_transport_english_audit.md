# Track B: exact canonical ages across physical sort changes

## Statement and proof, before Lean implementation

Fix any finite pool P of actual original vertices, a Boolean graph E, and
complete passing columns c(p,t) on d old sorts. Let pi map e new sorts to d old
sorts. It may identify children, omit old sorts, and combine these operations.
Write B for the full old-column raw bound, and B' for the bound formed using
c'(p,u)=c(p,pi(u)). For every nonempty admissible new support U,

    G_B'(U) = G_B(pi[U]).

This concerns the genuine normalized integer-witness canonicalizer, not just
the literal raw bounds. All old originals in P contribute, including active
gap vertices and reserved or selected originals.

The existing exact common-neighbourhood identity gives B'(U)=B(pi[U]). The
physical raw bound B is support-monotone: enlarging a support shrinks its
common-neighbour pool, hence cannot increase its clique capacity and cannot
decrease its raw allowance. The arbitrary-map canonical transport theorem
therefore applies. Its proof aggregates child weights in each parent fibre;
it never duplicates a parent's weight into all children. A preimage can be
too large to be an admissible support, so the proof first discards every
zero-weight child. The remaining positive support has cardinality at most
the normalized total, which is at most ell-1. For the opposite direction,
choose one child in U for each parent in pi[U] and place its parent's weight
there. All other children receive zero. Every support constraint is checked.

## Repeated changes of sorts

For maps sigma : Fin f -> Fin e and pi : Fin e -> Fin d, successive pullbacks
of complete columns are the same complete column as the pullback by pi o
sigma. The image of each admissible support is exactly pi[sigma[U]]. Applying
the physical equality gives the canonical value after both changes directly
from the original canonical age. This handles deletion followed by splitting,
splitting followed by deletion, and repeated noninjective refinements without
assuming that a raw bound is already a graph age.

## Neutral insertion after a sort change

Suppose the existing all-support mutual-neighbour capacity budgets make the
next actual original b age-neutral on the old sort domain. The already proved
raw budget transfer makes it neutral on the pulled-back domain as well. The
new canonical transport identity then identifies its resulting canonical
age with the original old-domain age evaluated at pi[U]. This closes the
dimension-change gap in the previously fixed-dimension neutral insertion
lemma; it does not prove that an arbitrary prescribed pivot is neutral.

## Target ages at an active pivot

If F is a genuine positive old graph age, the pullback F'(U)=F(pi[U]) is a
genuine positive new graph age. This follows from the same explicit witness
lifting, including all supports. Thus the active-pivot budget theorem can
be applied to F' without separately assuming its graph-age consistency.
For arbitrary complete protected background columns a and pivot bits beta,
the target F' lies below the actual next canonical age if and only if, for
every new admissible support U,

    cap(X(U)) + F(pi[U]) <= ell-1,

and, when beta is positive on every element of U,

    1 + cap(Y(U)) + F(pi[U]) <= ell-1.

Here X and Y are the complete actual nonpivot and mutually linked pools from
the existing active-pivot theorem. They include every nonpivot original below
the protected cutoff. This is an exact transfer of that theorem to the new
sort domain, not a discharge of the displayed inequalities for diary choices.

## Independent audit and scope

1. pi need not be injective or surjective. Distinct children may have the same
   parent, but integer weights are aggregated rather than copied.
2. Actual columns are pulled back on the entire original pool; preserving
   selected columns alone would not imply the physical raw identity.
3. Normalized support cardinality must be checked after deleting zero weights.
   The complete preimage of an old support can have more than ell-1 elements.
4. Zero raw bounds are allowed in the canonical transport theorem. Positivity
   is only imposed when using a genuine target age in the pivot budget test.
5. Support monotonicity is essential for omitted sorts. For ell=3, take two
   old sorts with B({0})=B({1})=2 and B({0,1})=1. Keeping only sort 0 gives
   new canonical value 2, whereas the old singleton canonical value is 1.
   Such a nonmonotone B cannot be an actual complete old-column raw bound.
6. Simultaneous mixed-support constraints remain essential; singleton
   feasibility alone still does not preserve the joint continuation age.
7. This proves the finite ordinary-L age component of a sort change. Auxiliary
   E relations, dependent Kpt source identities, I1/I2/I3, corrected B3, the
   prescribed infinite diary schedule and the global BRD theorem remain open.

## Verification completed: 20 November 2026

The exact source of `Kk/PhysicalCanonicalSortTransport.lean` passed the full
hosted gate in [PR #414](https://github.com/janhubicka/lean-kk/pull/414),
[run 44778772393](https://github.com/janhubicka/lean-kk/actions/runs/44778772393),
at head `a433ad84f3881da535ee3e7164ff32e3337d2c3c`: the complete
**9,709-job build**, parser self-test, and **953 exact named transitive-axiom
reports** all passed, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx` or custom axiom is accepted. The proof, imports,
and audit scripts are unchanged from that tested snapshot.

See the [dated evidence record](audits/2026-11-20-track-b-canonical-splits.json)
for hashes and endpoint names. This is a hosted result; the optional local
cold build was stopped after it passed, so no local full gate is claimed.
These finite transport results do not justify a global manuscript mark.
