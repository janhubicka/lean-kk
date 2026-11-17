# Track F — choose a rank-large daughter fan after any finite collection of previous source types

17 November 2026. English-first proof and adversarial checks, committed before Lean. Uses only the verified actual chronological Henson finite one-type tree, rank-large cone monotonicity, verified finite-fan theorem, and exact zero-padding marker-disjointness. It does NOT assume any published diary BRD characterization or global multi-sort synchronization.

## Statement

Fix actual graph edge table E, a consistent genuine finite Henson one-type u of positive ZERO-BASED rank n+1, a set S of types which is (n+1)-large at u, any finite set A of PREVIOUSLY CHOSEN source types (which may come from DIFFERENT source roots, ranks, and fibre sets), and for each a∈A an arbitrary old root node R(a) used to define its fresh positive-marker set `a.neighbours \ R(a).neighbours`.

For any prescribed k, find a family G of k lower-rank type nodes g extending u, with rank(g)=n and S n-large at g, such that:

1. All distinct g,h∈G have NO common extension cone and have pairwise-disjoint fresh markers relative to u;
2. For every previous a∈A and new g∈G, `(a.neighbours \ R(a).neighbours)` is disjoint from `(g.neighbours \ u.neighbours)`.

**No assumption about the old collection A being rank-large, internally compatible, or sharing a common root is needed.** Its members simply have finite original prefix heights.

## Proof

Let H=max(u.level,1+max{a.level:a∈A}). Zero-pad u to H; its old-neighbourhood set and rank are unchanged, and S remains (n+1)-large on that same-rank cone by verified monotonicity.

Apply the verified `rank_large_finite_fan S n zeroPad(u,H) k`. It gives k rank-n S-large descendants g above that padding, pairwise incompatible and internally fresh-marker-disjoint relative to the padding. Since padding does not change u.neighbours, those internal markers are precisely fresh markers relative to u.

Every old a∈A has a.level<H. Every g extends the zero-padding of u at H, so its positive bits below H are EXACTLY u.neighbours (including every zero bit outside u.neighbours). Thus any marker belonging to a.neighbours\R(a).neighbours lies below H, whereas no marker belonging to g.neighbours\u.neighbours lies below H. These sets are disjoint, by the previously kernel-verified cross-root `fresh_markers_disjoint_of_later_zeroPad` lemma. The choice of R(a) has no effect on validity.

## Hostile checks

1. A common branch prefix / source root for previously selected nodes is NOT assumed; temporal zero-padding is sufficient for cross-disjointness.
2. The rank of each old a may be zero, high, or unrelated to n; its only role is a finite height.
3. The root R(a) need not extend into a for this pure set-theoretic marker disjointness statement; this is stronger than the later geometric application where it will.
4. A's marker set may contain some u-old positive neighbours; new g markers are specifically outside u.neighbours, so disjointness still holds.
5. Internal fan disjointness is initially expressed relative to zeroPad u at H. The proof MUST rewrite these neighbourhood sets to the old unpadded u.neighbours; simply asserting that the two markers are 'the same' without a definitional equality check would be a formalization gap.
6. The new family nodes may extend beyond H by different amounts; no assertion that their completed original coding vertices are mutually adjacent is made.
7. The theorem constructs hypothetical consistent daughter type nodes. It does not claim each daughter itself is an ACTUAL original coding node; S-large descendant cones later contain genuine S members when S consists of actual coding nodes.
8. The theorem preserves the whole recursive S-largeness condition on each new daughter; merely obtaining k different lower-rank nodes is insufficient.
9. Repeatedly applying this lemma to an arbitrary finite list of active sorts would construct a global temporal marker-disjoint schedule, but the resulting graph-age compatibility and source-to-target fibre synchronization must still be proved separately.

## Lean acceptance

Formalize a single safe additional-family theorem with explicit cardinality k, per-daughter rank and largeness, internal incompatible cones and internal marker disjointness, and cross-marker disjointness against every prior finite a relative to arbitrary root R(a). Do not introduce new assumptions about Henson OnePointLeftDense, diary histories, or target embeddings. Exact-head Lean build and strict standard-only named axiom gate required.