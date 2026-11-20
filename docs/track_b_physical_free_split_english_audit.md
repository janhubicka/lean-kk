# Track B: a constructed free split preserves the complete canonical age

## Statement (English proof before Lean)

Fix the actual complete original prefix P=[0,b), arbitrary full passing
columns c(p,t) on its d sorts, and an old genuine positive integer graph age
F=G_B, where B is the actual full-prefix raw bound. Let pi send e new sorts
to the d old sorts; duplication and deletion are allowed. Choose one genuine
new original v>=b that has no edges in either direction to P. For any H>v,
the new complete column C on [0,H) is c(p,pi(u)) for p<b, beta(u) at v,
and zero at every other p>=b. In particular, no protected old original is
deleted and no old active, selected, reserved or parameter column is reset.

Assume, for every admissible nonempty new support U on which beta is all
positive, that F(pi[U])<=ell-2. Then the entire new canonical age is

    G_new(U)=F(pi[U])

on every admissible support, including mixed supports. The new finite
future exists in the same normalized left-dense Henson graph, with one
embedding and cutoff carrying the full numerical-stage certificate.

For a single new positive daughter u*, take beta(u)=(u=u*). Only the
singleton {u*} is a nonempty all-positive support. Thus the sole safety
condition is F({pi(u*)})<=ell-2. With pi the ordinary two-daughter parent
map, this is precisely the nonmaximal free split. The parent map itself
needs no injectivity or surjectivity assumption.

## Proof

For U let X be the actual old common-neighbour pool for pi[U]. The exact
pointed-column pool formula says that the new pool is X when some beta bit
on U is zero, and X union {v} otherwise. Since v has no old neighbours,
its mutual-link pool inside X is empty. The exact new capacity is therefore
rho(X) in the first case and max(rho(X),1) in the second. Natural subtraction
gives, respectively,

    B_new(U)=B(pi[U]),
    B_new(U)=min(B(pi[U]),ell-2).

This identity uses ell>=2; the empty-link and singleton-pivot cases remain
valid when X is empty. It is an all-support equality of actual raw bounds.

The canonical transport theorem proves that F'(U)=F(pi[U]) is a genuine
positive new graph age and equals the canonical age before imposing beta.
Because F<=B, the displayed raw formula and the all-positive cap imply
F'<=B_new. The greatest-age-below-raw property gives F'<=G_new. Conversely
B_new<=B pulled back; G_new is a genuine age (it lies above F'), so the
same greatest-age property puts G_new below G_(B pulled back)=F'. Thus
G_new=F'. No all-support pivot-budget hypothesis is assumed: it is derived
from the free-pivot geometry and the stated canonical cap.

To construct v, prescribe the zero neighbour column on P. Its complete
(ell-1)-neighbour clique test is false because ell-1>0 and there are no
positive neighbours. The stipulated one-point left density supplies an
actual v>=b with both edge directions zero to every original below v.
Choose H=v+1. Apply the existing finite universal numerical-stage theorem
to C at H. It supplies one shared f,M, fixes every original below H, and
realizes all feasible clique vectors and complete original columns. Thus
the same v distinguishes the two daughter types and every protected old
original has its prescribed old column to all new future witnesses.

## Adversarial audit before formalization

1. The pivot is a new isolated marker, not an already selected vertex of an
   arbitrary old sort. Imposing zero old neighbours on a prechosen pivot
   would be invalid; its existence is constructed by left density.
2. Every old original p<b is protected with its full column c(p,pi(u)).
   Zero new columns are assigned only outside that protected prefix and
   away from v. Any previous witness to retain must already lie below b.
3. The arbitrary physical graph E is unchanged. The gap-zero column does
   not erase actual originals or their edges from E.
4. The complete support condition is required when beta has several positive
   sorts. Singleton safety does not suffice in that generality.
5. For beta positive at exactly one daughter, nonempty all-positive support
   really is that singleton. The single parent cap then discharges every
   positive-support condition, not merely a selected subset of them.
6. rho(X)=0 is allowed. Adding v then changes the raw bound from ell-1 to
   ell-2; canonical preservation still holds when the actual canonical
   target is already <=ell-2 at that support.
7. The proof retains natural truncated subtraction. ell>=2 is explicit.
8. F must be the old complete canonical age and must be positive genuine
   graph age. No raw-age consistency or parent injectivity is assumed.
9. The equality is of the full canonical age. It need not assert raw
   equality: a redundant raw bound can decrease under the new marker.
10. A maximal parent F({j})=ell-1 does not meet the nonmaximal split
    condition; its positive daughter acquires an actual singleton cap.
11. The finite Henson witness retains one common embedding and numerical
    cutoff, rather than separately existential edge/profile witnesses.
12. The result establishes a finite ordinary-L split. It does not yet
    synchronize auxiliary E, the dependent Kpt closure, I1/I2/I3/B3,
    occurrence-independent microdiaries or a common labelled inverse orbit.

Verification remains pending until Lean compilation and named transitive
axiom checks pass. No global resolved-copy or BRD marker is promoted.
