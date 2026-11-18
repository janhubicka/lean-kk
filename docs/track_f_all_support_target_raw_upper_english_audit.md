# Track F — every target mixed raw capacity is bounded by the source profile

18 November 2026. English-first proof and adversarial audit committed **before Lean**. This formalizes one direction of the still-pending full multi-sort synchronization lemma. No diary characterization, published BRD count, or equal target/source age is assumed.

## The actual sorted graph setting

Fix ell≥2, actual source and target directed Boolean edge tables Esrc,Etgt, an injective INDUCED embedding e:Nat→Nat, and d finite labelled source/target one-type pairs. Each source root u_i is a genuine HensonOneType ell Esrc over common source prefix m, and each target v_i is a genuine HensonOneType ell Etgt over common target prefix H. For EVERY i, the exact set of ACTUAL source coding nodes mapping into target prefix type v_i is rank(u_i)-large above u_i. Choose H after every e(c) with c in the finite source-old neighbour set u_i.neighbours.

Let U_i=u_i.neighbours⊆[0,m), and V_i=v_i.neighbours⊆[0,H). On any NONEMPTY support S⊆Fin d, its actual common-old-neighbour pool is Csrc(S)={x<m:for all i∈S, x∈U_i} and Ctgt(S)={y<H:for all i∈S, y∈V_i}. Define raw support ages bsrc(S)=ell−1−cap_Esrc(Csrc(S)), btgt(S)=ell−1−cap_Etgt(Ctgt(S)) where cap is the true largest directed old clique (Nat subtraction is truncated but monotone).

## Step A: the source-old positive image inclusion at every sort

The verified Large.has_member theorem supplies for each i an ACTUAL source coding vertex x_i in the fibre of v_i, with its source type extending u_i. Since all e(c) for c∈U_i lie below H, the already verified Track F theorem `old_source_neighbour_images_in_target` (merged PR #297) proves

    e[U_i] ⊆ V_i  for every source sort i.

No ordering of the embedding e is assumed. The chosen x_i may differ across sorts; their existence alone suffices for this old-support obstruction transfer.

## Step B: the common pool image inclusion

Fix nonempty S and x∈Csrc(S). Then x∈U_i for every i∈S, so e(x)∈V_i for every i∈S. Choosing one i0∈S guarantees e(x)<H because V_i0 is a genuine target old-neighbour set below H. Hence

    e[Csrc(S)] ⊆ Ctgt(S).

The nonemptiness hypothesis is essential: on the EMPTY support, the common pool is the entire prefix [0,m), and e may map some old source vertices beyond H even when all old POSITIVE neighbour images are below H.

## Step C: exact graph clique transport and raw age inequality

The already verified theorem `finiteDirectedCliqueCapacity_induced_image_eq` (finite clique image invariance for injective induced maps) gives cap_Esrc(Csrc(S))=cap_Etgt(e[Csrc(S)]). By monotonicity under the inclusion in Step B, this is at most cap_Etgt(Ctgt(S)). Therefore

    btgt(S) ≤ bsrc(S)

for EVERY NONEMPTY support S, including triples and higher intersections.

This gives the TARGET RAW AGE NO GREATER THAN SOURCE RAW AGE, the obstruction/certificate half of the full profile comparison. The numerical canonical mixed-support ages may involve interactions of constraints; do NOT claim canonical target profile equality from this lemma. The reverse inequality and full equality require genuine multi-sort finite GRAPH richness among the selected coding-node fibres, which remains open.

## Hostile audit

1. The source/target old prefixes need NOT be related by e; only the finite old positive neighbour images are required below the target prefix. e need not preserve chronological order.
2. Each fibre must contain an ACTUAL source coding vertex, not merely a hypothetical finite type. The rank-large hypothesis supplies such a vertex; it is stronger than bare consistency.
3. The theorem is on NONEMPTY supports. For S=∅ the source common pool is [0,m) and image inclusion can fail.
4. Each target old neighbour set V_i is known to lie below H from the actual HensonOneType certificate. This supplies the finite prefix bound without an additional arbitrary assumption.
5. Full *induced* edge preservation and injectivity of e are needed for exact clique-capacity transport; a mere edge-preserving map may change clique numbers.
6. Distinct source coordinates need not be compatible in the sense of realizing all mixed graphs for this one-sided result. Their separate large fibres suffice.
7. Source and target singleton RANK equality is not used; the raw inequality is valid even when ranks mismatch. Using previously verified same-rank continuation supplies such equality in intended applications.
8. The raw bound uses actual common-old-neighbour clique capacity, NOT the size of the intersection nor a speculative canonical value.
9. The target has possibly MORE common old neighbours, making its raw age LESS THAN or equal source raw age. This is the only valid direction before source-fibre joint richness.
10. This proves no diary-history persistence, no full profile equality, and no exact K4-free BRD number.

## Lean acceptance

Prove image inclusion of common old pools under coordinatewise neighbour-image inclusion. Prove the all-nonempty-support raw-age inequality using verified exact induced clique capacity transport. Then discharge neighbour-image inclusion from exact sourceCodingFibre largeness at every coordinate, using `Large.has_member` and merged `old_source_neighbour_images_in_target`. Strict exact-head targeted Lean and standard-only transitive axiom gate. Annotate only editable olive synchronization proof and keep the global `Full tuple profile synchronization` marker pending.