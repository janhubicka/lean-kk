# Track B — protected active passing columns (English proof before Lean)

## Correction to the 910-checkpoint limitation

The old pointed continuation assigns **zero** future passing bits to every protected original other than the pivot in [b,H). Its second embedding fixes their vertices, but need not preserve their designated active later passing roles. We now retain an arbitrary complete background passing column on ALL those originals. This is a genuine strengthening of the finite ordinary-L construction, not a claim of full Kpt source coherence.

## The exact finite lemma

Let E be any directed Boolean graph, H a finite actual original cutoff, and v<H a fixed genuine pivot. Let a(p,u) be ANY complete typed background column, possibly positive on arbitrarily many protected old originals. Choose a pivot passing map beta(u), and put

    C(p,u)= beta(u) if p=v; else a(p,u).

For a nonempty support U of sorts, define

    X(U)={p<H: p != v and forall u in U, a(p,u)=1},
    Y(U)={p in X(U): E(p,v)=E(v,p)=1},
    rho(Z)=maximum size of a directed clique in Z (including empty).

Then the COMPLETE original support pool under C is X(U) union {v} when all beta bits in U are 1, and X(U) otherwise. Its exact clique capacity is

    rho_new(U) = max(rho(X(U)), 1+rho(Y(U))) if all beta(U)=1,
                 rho(X(U)) otherwise.

Proof: by a pointwise membership check, a nonpivot original p passes precisely when it belongs to X. The pivot passes precisely when every beta bit is positive. Any clique through v consists of v and a bilateral clique in X, precisely a clique in Y. Every finite maximum exists. No gap original is deleted from E or excluded from the full prefix; positive active gaps contribute honestly to X and Y.

Thus the raw age on every support U is ell-1-rho_new(U), with natural subtraction. Canonicalize the entire support function jointly; never assume canonicalization commutes with maximum, parent maps or separate supports.

## Old-sort parent/refinement and active gaps

If the old cut is b<=v<H, the old typed column is c(p,t) for p<b, and pi maps new sorts to old sorts, choose an arbitrary complete gap passing function g(p,u). Put

    C(p,u)=c(p,pi(u)) if p<b;
           beta(u)    if p=v;
           g(p,u)     otherwise.

The disjoint cases are well-defined because b<=v. For every p in [b,H) other than v, the new future sees exactly g(p,u), including nonzero columns on any earlier selected witness, split/coding parameter or reserved original. Zero g recovers the previous theorem. The general exact-capacity lemma applies to the full background a(p,u) formed from c and g.

Apply the existing finite Henson numerical-stage realization theorem to the explicitly defined column C and cutoff H. It returns ONE embedding f and cutoff M with complete old/gap numeric-L columns, profile realization and carrier bounds. It fixes all originals p<H, including pivot v and any older selected witnesses. Their prescribed future ordinary-L incidences are now g, not forced zero. The theorem does not identify corresponding old active sort labels or preserve auxiliary E, closure or corrected B3 across successive numeric stages.

## Adversarial audit

1. The pivot must be excluded from X even if a(v,u) is one, to avoid double counting.
2. The complete physical original prefix is [0,H), including all actual gap vertices.
3. Mutual links require E(p,v)=E(v,p)=true, not a single directed arc.
4. Arbitrary parent map pi may identify sorts; use passing on U, not assumptions on cardinality of its image.
5. Nonempty U is essential for earlier zero-gap simplifications; the general membership identity also works for empty U, but age supports are nonempty.
6. If beta is not all positive, v is absent from the support pool, even though some children pass.
7. When X=empty and beta positive, capacity one is witnessed by the singleton {v}.
8. Positive protected gaps can increase capacity, so the old formula based only on the pre-b prefix is invalid unless they are neutral.
9. The exact clique-capacity formula does not require global K_ell-free safety; Henson realizability requires the already explicit normalized-age/left-density assumptions.
10. Each labelled new sort may have zero feasible witnesses. No positivity is inferred from merely defining its column.
11. Exact one-point feasibility does not settle mixed vector feasibility; the K4 seven-old-original pair counterexample remains relevant.
12. Henson finite realization uses ONE common f,M, not a conjunction of independently selected existential witnesses.
13. Fixing old graph vertices does not imply maintaining the previous numeric-H source nodes at their old coordinates.
14. The full parameter-closed I1/I2/I3/B3 and common labelled inverse-source orbit still require a separate transport lemma.
15. No unbounded resolved copy or global exact BRD claim is obtained.

## Concrete obstruction to the zero-gap shortcut

In K4, let x,y be protected gap originals forming an edge, both g-positive on U. If beta is zero on some u in U, X includes {x,y} and capacity is at least two, while forcing gap-zero incorrectly gives capacity zero. If beta is all positive and v is adjacent to x,y in both directions, then Y includes the edge, so the complete support capacity is at least three: the new raw bound is zero. This illustrates why retaining the active-gap columns is essential.

## Formalization gate

Formalize the exact pool/capacity/raw identities first; then package a finite Henson stage realizing all compatible profiles with the same protected real vertices and arbitrary prescribed g columns. CI must pass full build and named standard-only transitive-axiom check before green manuscript marks. Preserve black text and existing TODOs.
