# Track B: critical-count control of finite old reference ages and the next physical cover
**17 November 2026 — English proof and adversarial audit, before Lean.**

## Already kernel-checked input

The full one-original critical-support and finite telescope are validated in lean-kk/main (PRs #262 and #258; exact-head full 837/841 named-axiom checks). For a **fixed** directed old-original graph E, fixed sort dimension d, and unchanged full old-to-future typed columns c, denote

\[
 B_n(U)=\ell-1\mathbin{\dot-}\rho_E(X_n(U)),\qquad
 X_n(U)=\{p<n:\forall t\in U,\ c(p,t)=1\}.
\]
For the full chronological original interval [b,b+m), let C_{b,m}(U) be the **actual** critical-original count from Kk.originalCriticalCount. The verified theorem says
\[
 B_{b+m}(U)=B_b(U)\mathbin{\dot-}C_{b,m}(U).
\]

## New theorem A — physical forbidden-free prefixes eliminate saturation

Assume the **actual final original prefix** [0,b+m) has no K_ell, expressed by the executable complete finite pool test
\[
 \mathrm{finitePoolCliqueCheck}(E,\ell,[0,b+m))=\mathrm{false}.
\]
The genuine old common-neighbour pool X_{b+m}(U) is a subset of that final original prefix, so its clique capacity is < ell. Therefore B_{b+m}(U) >= 1. Combine this with the exact telescope:
\[
 B_b(U)=C_{b,m}(U)+B_{b+m}(U).
\]
This is an ordinary natural-number equality, not truncated subtraction, because the final raw age is strictly positive and truncation cannot have saturated. In particular C_{b,m}(U) < B_b(U) and
\[
 C_{b,m}(U)=0\quad\Longleftrightarrow\quad B_{b+m}(U)=B_b(U).
\]
All statements are pointwise for **each admissible nonempty support**. The prefix test may equivalently be obtained from the already proved cliqueFree_prefix_iff_all_finite_neighbour_certificates when the graph is symmetric loop-free and every actual previous original step passed its complete negative neighbourhood test. Neither direction is assumed from a selected-front shadow.

## New theorem B — global neutral reference age from the count

Suppose, for every admissible nonempty future support U, C_{b,m}(U)=0. The verified telescope directly gives equality of the **whole raw old-column bound functions**, hence equality of their integer-witness canonicalizers:
\[
 G_{B_{b+m}}=G_{B_b}.
\]
No K_ell-free hypothesis is needed for the *sufficient* direction. Under the final true K_ell-free prefix condition above, pointwise raw equality is equivalent to pointwise zero critical counts; equality of **canonicalized** ages alone is still NOT equivalent to zero criticality.

If the pre-interval canonical age is a specified upper, the exact pointwise hPrior invariant remains true after the interval:
\[
 G_{B_b}=\mathrm{upper}
 \quad\Longrightarrow\quad
 G_{B_{b+m}}=\mathrm{upper}.
\]

## New theorem C — compose neutral interval with a genuine finite physical cover step

The already certified henson_leftDense_exists_physical_finite_canonical_cover_stage is a **genuine fixed-Henson original** construction, assuming the actual old canonical age equals upper pointwise at its starting cut. Apply theorem B to get that very hypothesis at b+m from hPrior at b and zero critical counts on [b,b+m). Given exactly the remaining hypotheses of that physical stage theorem — normalized Henson forbidden-family avoidance on the fixed original graph, OnePointLeftDense, ell>=2, d>0, an age cover lower lessdot upper at support T with ell=lower(T)+r+1 and upper(T)=lower(T)+1 — the physical stage yields a reserved original clique Q of size r after b+m, a real cutoff F including every intervening gap, old-to-reserved nonedges in **both** directions, and a new column whose *entire* canonical old-prefix age is lower; its simultaneous positive-support top future is an actual numerical H-object.

This is a valid **finite neutral stretch + one cover** composition. It assumes that a single unchanged full typed column c produced zero critical events along that stretch; it does *not* construct those earlier chronological originals or prove their columns can be chosen recursively to make every intended interval neutral. The physical cover theorem already constructs the new finite clique block when its explicit hypotheses hold. Reapplying this composite theorem indefinitely requires updated columns and new critical-count hypotheses at each step.

## Adversarial checks

1. The count is over every **actual original** in the interval, including split/coding-parameter originals and skipped gaps; not just selected tops.
2. The same entire typed column c is used at the initial and final cuts. A diary split that changes its sort dimension cannot be hidden inside this theorem.
3. Raw age positivity requires the true final original pool to be K_ell-free; without it, saturated truncated subtraction can hide critical events.
4. Zero critical counts imply literal raw equality **even in unsafe graphs**. The converse needs physical safety, and it is false for canonical-age equality alone.
5. Every admissible support must be checked, not only the support of the next intended cover.
6. The Henson cover stage takes the real hPrior=upper invariant; it does not infer this merely from an abstract age-cover identity.
7. Its actual fresh block may be nonconsecutive; all original gaps before the new cutoff are accounted for by the stage's supportBlockGappedColumn.
8. The old age from a neutral interval still uses the old full column c; the subsequent cover stage changes columns on new reserved originals, explicitly and nontrivially.
9. The full physical cover stage produces one finite top-pool witness, not a simultaneous *infinite* schedule and not one common inverse-source orbit.
10. A raw-capacity decrease at many supports is not automatically one canonical graph-age cover; the age step uses the separately proved IsolatedSupportCanonicalAge normalization.
11. The numeric H ordinary-L source does not decide the Kpt auxiliary E, complete old/upper L+ I1/I2/I3/(B3) microevents, or relative-continuation corrected-B3 loss. The concrete K4 q2 auxiliary cuts 10/22 remain genuine regressions.
12. The full bounded resolved copy and the optimal BRD upper/lower bounds remain UNPROVED by this finite composition.

## Acceptance

English mathematics first, then kernel-check separate named Lean endpoints with exact-head full build, strict transitive-axiom audit and only the standard trio propext, Classical.choice, Quot.sound. Source-precise manuscript component marks only after validation. Keep frozen black prose unchanged and add olive TODOs for the unbounded application; do not upgrade the global bounded-copy or BRD statements.
