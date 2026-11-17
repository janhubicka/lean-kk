# Track F — exact finite labelled-clique transfer under daughter-to-parent collapse

16 November 2026. English proof and adversarial audit **before Lean**. This is an independent finite-combinatorial step of the one-type richness induction; no diary count or global BRD theorem is used.

## Precise setting

Let D be a finite refined set of daughter sorts, P a finite set of parent sorts, and π:D→P their collapse map. The map π need **not** be injective: multiple daughter branches can originate from the same old parent. Let B be a finite set of target vertices with daughter label δ:B→D and parent label π∘δ. For a nonempty support S⊆D define the daughter clique count N_D(S)=|{v∈B: δ(v)∈S}| and for T⊆P define N_P(T)=|{v∈B: π(δ(v))∈T}|.

Assume: (1) the original graph B satisfies N_P(T)≤b_P(T) for each nonempty T⊆P; (2) every daughter has at most one assigned vertex, N_D({i})≤1; (3) every daughter singleton raw age bound b_D({i})≥1 (the daughter type is admissible); and (4) for all refined supports S with |S|≥2, the exact new mixed RAW bound is b_D(S)=b_P(π[S]).

**Claim:** B satisfies N_D(S)≤b_D(S) for every nonempty refined support S.

**Proof.** If S={i}, assumption (2) gives N_D(S)≤1≤b_D({i}). Otherwise |S|≥2. The subset of B with daughter sort in S is contained in the subset with parent sort in π[S], so N_D(S)≤N_P(π[S])≤b_P(π[S])=b_D(S). Nonemptiness of S makes π[S] nonempty. That proves every raw constraint. An already verified graph-age canonicalizer preserves all finite feasible labelled clique multiplicity vectors, so the same B also satisfies the canonicalized refined age.

## Genuine old-neighbourhood realization of the mixed-bound premise

Let every parent p have a fixed old-neighbour set U_p⊆[0,m), and every daughter i have a fresh marker set V_i⊆[m,N), pairwise disjoint. Define its actual old-neighbourhood W_i=U_{π i}∪V_i. The already verified disjoint-marker theorem (PR #237) shows that on any refined support S with at least two distinct indices, its complete common-old-neighbour pool equals the pool for the pulled-back old sets U_{π i}. By quantifying over the image π[S], this old pool equals exactly the original common-neighbour pool on π[S]. Their directed old-clique capacities, and hence their raw age bounds, are equal. This gives premise (4) geometrically without assuming canonical mixed ages unchanged.

## Adversarial checks

1. π can identify children: if two daughters share a parent, the old parent inequality controls their TOTAL multiplicity, not independent unrelated bounds.
2. The one-vertex-per-daughter hypothesis cannot be dropped. A daughter whose raw bound becomes one cannot safely host two vertices, even if the original parent had larger capacity.
3. The new singleton bound ≥1 is indispensable: otherwise assigning one vertex to an inadmissible daughter violates the new raw age.
4. The common-neighbour identity applies only to supports with two distinct sorts and pairwise disjoint fresh sets; singleton supports may have new clique obstructions.
5. The actual mixed RAW bound is the one preserved. Canonicalization can decrease mixed values, but preserves precisely the same set of feasible normalized labelled clique vectors.
6. Nonempty S is required: the empty-support convention is a different age-free object.
7. The graph B must satisfy EVERY old parent support inequality, not merely the top full support; multiple clique patterns may be excluded by sub-support restrictions.
8. This finite transfer does not establish that the required rank-large daughter fibres can be selected jointly for ALL parents, or that an arbitrary Henson subcopy contains the resulting prescribed finite history.

## Lean endpoints and application status

Formalize the collapse of actual common-neighbour pools, equality of the mixed actual raw age, and the finite labelled-clique support-count transfer under (1)-(4). Use the existing Finset cardinality and old integer graph-age vector theorems; no new axioms. Each endpoint needs a dedicated exact-head build and standard-only axiom audit. Later geometry must verify the marker sets exist with the displayed disjointness and singleton bounds. The global richness/BRD statements remain pending.