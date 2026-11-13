# KK Track A — relative marked-front finite age bridge (English proof and hostile audit)

**13 November 2026.** This note precedes formalization in
`Kk/RelativeMarkedFrontAge.lean`. It concerns **ordinary graph L** only.
Track B constructs the chronological stage, Track C supplies full auxiliary
H+ source data, and Track G owns manuscript validation marks.

## Exact conditional theorem

Fix a threshold `ell`, a finite set of types `D`, a support
`T ⊆ D`, finite coordinate pools `P,Q,G,W`, and a label map
`tau : W → D` (possibly many distinct vertices of the same type).
Write `U_T = {w∈W : tau(w)∈T}`. Let `L` be a Boolean directed graph
table covering these pools, and `A` a **separate reference** table
representing the prescribed old-continuation graph on `P∪W`.

Assume the **following actual statements, not inferred age conclusions**:

1. `Q ∩ W = ∅` (hence `Q ∩ U_T = ∅`).
2. All ordered `L(p,q)` for `p∈P,q∈Q` are zero.
3. All ordered `L(g,w)` for `g∈G,w∈W` are zero. The pool G
   includes *every* unused old coordinate up to the tested cut, including
   real copies of intervening originals and all dummy coordinates.
4. **For every marked future vertex** `w∈W`, for every reserved
   coordinate `q∈Q`, *both*
   `L(q,w)=L(w,q)=1[tau(w)∈T]`. In particular all outside-support
   bits are zero: checking only one selected target is not enough.
5. The complete past `P∪Q∪G` contains no directed `K_ell`.
6. On every ordered off-diagonal pair of `P∪W`, `L=A`.
   It is enough to check all four subrectangles
   `P×P`, `P×W`, `W×P`, `W×W`; these include the full old-to-future
   columns and arbitrary within-future graph edges, *not just a chosen
   actual list of future originals*.

Then, with `cap_L(V)` denoting the maximum cardinality of an
off-diagonal directed clique in `V`,

```text
K_ell-free_L(P ∪ Q ∪ G ∪ W)
  iff
K_ell-free_A(P ∪ W) and cap_L(Q) + cap_L(U_T) < ell.
```

This is an exact **per-pattern** theorem; it applies to every finite
labelled W and every choice of its internal L edges for which the explicit
four subrectangles and full-column hypotheses hold. It does not assert
that a single fixed ambient Henson enumeration realizes every such
pattern with all requested columns.

## Proof (before Lean)

Every L-clique meeting W but no Q avoids G\W, by (3), and hence lies
in P∪W. Every L-clique meeting Q and W avoids P\Q by (2) and avoids
G\W by (3). Its W-elements must all lie in U_T by (4), so it lies in
Q∪U_T. A clique missing W lies in the safe past by (5). This classification
uses the ordered-edge convention; there is no assumption that the
entire Q is itself a clique or that P,G,W form a pairwise disjoint
partition. The only disjointness needed in the additive capacity formula
is Q∩U_T=∅.

Since *all crossing directions* from Q to U_T are present, every
maximal clique of Q and every maximal clique of U_T can be united.
Conversely any clique in Q∪U_T splits into cliques in the two pools.
Therefore cap_L(Q∪U_T)=cap_L(Q)+cap_L(U_T). By classification,
the enlarged table is free exactly when the old-continuation table
L|_(P∪W) is free and this sum is < ell. Condition (6) allows us to
replace the former check by the independent reference table A.
This proves both directions without asserting existence of the
specified L table.

## Physical numerical-H specialization and its limit

For **consecutive** reserved originals N,...,N+r−1, existing
`Kk.NumericHReservedPrefixCapacity` computes the genuine L-copy
capacity at pivot (a,g) as
`cap_L(Q) = a` if `g<a`, and `a+1` otherwise, assuming
`a<r≤k+1`, `g≤k`, original clique edges and symmetry.
Together with the conditional theorem this yields
`cap_L(U_T) + (if g<a then a else a+1) < ell`.
The existing `NumericHReservedPrefixGluing` is the exact low-level
physical counterpart; the present module must add the *labelled
entire-front* filter and the separate reference-age comparison.

**Nonconsecutive-block caveat, essential for Track B:** the current
numeric-capacity specialization uses originals `N+b`. Left-dense
selection usually produces increasing originals `q_0<...<q_{r-1}`
with gaps, *not necessarily consecutive labels*. The same generation
argument should transport along the strictly increasing q-map, but
a new exact ordered-block embedding theorem (or a rigorous reduction)
must be supplied before using the consecutive formula on the recursive
selection. No silent replacement of `q_b` by `N+b`.

**Prefix completeness caveat:** a full physical-prefix claim also
requires `P∪Q∪G = [0,m)` and full carrier membership, with every
gap-to-W zero. Without this equality the theorem only analyzes
the displayed finite pools, not the entire ambient prefix.

**Reference-age caveat:** equality with a genuine integer graph age F
must be established using the *full normalized clique-multiplicity
profile*. The abstract age-profile theorem does not automatically give
the reference-table agreement for an arbitrary old Henson prefix.
The fixed W's actual H edges cannot stand in for every freely chosen
labelled future pattern.

## Adversarial regressions / scope audit

1. **K3 P4 missing marked column:** old p=0, reserve q=1,
   other marked y=2, target marked x=3; graph edges are
   p–y, y–q, q–x. For T={x}, q–y=1 violates (4) because y∉T.
   The one-target proof controls q–x, but fails this whole-front test.
   The old age permits an x–y edge that the actual post-q age forbids.
   This does *not* refute a future schedule that enforces (4).
2. **Outside-support negative is essential.** If q–y=1 is allowed
   for y∉T, the formula can fail even when the designated target's
   positive column is correct.
3. **Both orientations:** directed clique membership checks both
   L(q,w) and L(w,q). One-sided support data is not enough.
4. **Exact capacity, not |U_T|:** W_T can contain many vertices
   but have a smaller clique number.
5. **Multiplicities:** tau need not be injective; two distinct future
   vertices may have the same sort.
6. **Past:** removing the safe-past test allows a forbidden clique
   entirely inside P∪Q∪G; neither RHS condition detects it.
7. **Gaps:** without all G-to-W zero columns a forbidden clique can
   use a forgotten gap vertex and some future vertices.
8. **Old reference agreement:** must include P×W and W×P as well
   as P×P and W×W; no existential one-point theorem supplies this
   simultaneously for a whole front.
9. **Boundaries:** empty W or T, ell=0, and non-clique Q are handled
   by the exact finite-clique-capacity interface. There is no implicit
   positivity hypothesis on ell in the generic theorem.
10. **No forbidden inference:** this ordinary L result does not
    validate auxiliary Kpt E, corrected B3, a common labelled
    inverse-source orbit, global resolved-copy existence, or any final
    BRD formula.

A separate bounded Python adversarial test generated 1,807 random
symmetric admissible finite gluings (ell=3,4,5, with random labels,
supports, gaps and internal W edges), and observed no violation of
the equivalence. This is *regression evidence only*, not formal
validation; the theorem still requires exact-head Lean compilation.

## Formalization checklist

* Prove finite-pool clique-check invariance under exact off-diagonal
  edge agreement, then derive agreement from the four subrectangles.
* Specialize the previously verified isolated-block gluing iff using
  `U_T=W.filter(tau(w)∈T)` and the numerical-H prefix capacity.
* Show the P4 outside-support required zero contradicts the actual q–y
  positive edge (as a named regression).
* Export named theorems with `#print axioms` and compile the module,
  then run full `lake build` and strict named standard-only axiom
  checks at the exact PR head.
* Keep the physical nonconsecutive schedule, prefix decomposition,
  integer-age adapter, and all global proof claims pending until their
  hypotheses have been proved. Do not edit `Kk.lean`, `kk.tex`,
  `validation.tex`, or the integration-owned axiom script here.
