# Track F — source-distinguishing old bits force distinct actual target-prefix fibres

17 November 2026. English proof and hostile audit before Lean. This isolates the DISTINCTNESS part of the still-pending full source/target multi-sort synchronization lemma, using only genuine source coding nodes and an injective induced embedding. It does NOT assume a diary theorem or a global Ramsey statement.

## Precise old-bit separation setting

Let Esrc,Etgt be actual directed ordinary graph adjacency tables. Let e:Nat→Nat be a map preserving every off-diagonal directed binary atom, with e injective when using it as an embedding (but the basic bit contradiction itself only needs edge preservation). Take two genuine source HensonOneType nodes u,v and an actual source index a strictly below both source levels, where the source old-neighbourhood bits differ: `(a∈u.neighbours) ≠ (a∈v.neighbours)`.

Suppose x and y are ACTUAL source coding nodes extending u and v respectively. Then their true source edges to the ORIGINAL vertex a differ: the first has Esrc(a,x.level)=decide(a∈u.neighbours), the second Esrc(a,y.level)=decide(a∈v.neighbours). All source indices are distinct because a is strictly earlier than x.level,y.level.

Under inducedness, the actual target edges at coordinate e(a) to the images e(x.level) and e(y.level) differ, even if e arbitrarily scrambles the order of originals. Therefore for any finite TARGET prefix H with e(a)<H, these two later target image vertices cannot have the SAME complete two-directed target H-prefix. In particular, they cannot both lie in the same exact `sourceCodingFibre` of a target HensonOneType whose level exceeds e(a).

## Formal statements

1. `different_source_bits_prevent_same_target_fibre`: for genuine source types u,v with a separating old coordinate a, and ACTUAL coding descendants x≥u,y≥v, it is IMPOSSIBLE for both x and y to lie in the same target coding-node fibre over a target prefix type t with e(a)<t.level, assuming induced preservation of ordinary edges. No target K_ell-free hypothesis is required: this is literal adjacency-bit equality.
2. `distinct_target_types_of_source_bit_difference`: if x≥u,y≥v belong to fibres over target types tx,ty at the SAME target level H>e(a), then tx≠ty. Suppose they were equal; then both would be in the SAME target fibre and contradict (1). The result makes a finite level H explicit and does not assume e preserves source order.

## Application to the pending synchronisation proof

For a FINITE tuple of pairwise distinct source types at a COMMON source level m, each pair has some old coordinate a<m with differing positive/negative bit. Since e is injective, choose a single finite target cutoff H beyond the finite image set of all these separating source originals. If for each source coordinate one can choose an ACTUAL source coding node in its source-to-target rank-large fibre and extend the target types to level H, the resulting target H-prefix types are pairwise distinct by (2). This handles the DISTINCTNESS obligation independently of the still harder full mixed-support graph-age equality.

## Hostile checks

1. Source types being distinct is not enough without a common old level or an explicitly supplied separating coordinate. If two types are at different levels, they may be compatible initial-segment extensions.
2. Both x and y MUST be ACTUAL coding originals; a hypothetical finite type with no physical coding original does not determine edges of Esrc at its own level.
3. The old coordinate a must be STRICTLY before both source types and hence strictly before both coding original indices, so induced off-diagonal equality applies; loop edges cannot be used.
4. The target cutoff must include e(a), i.e. e(a)<H. The embedding need not be monotone: H>a is not sufficient.
5. The selected images must both occur after H, guaranteed by membership in the exact target coding fibre; arbitrary source coding nodes not in the fibre do not suffice.
6. Old TRUE and FALSE bits matter: a distinguishing negative bit is as effective as a positive bit. The proof uses equality of exact Bool adjacency atoms, not merely positive-edge preservation.
7. The target types must be at the SAME target level H to turn indistinguishability into equality; without this the two target types may have one extending the other.
8. Distinct target prefixes alone do not establish full source/target graph-age profile synchronization or the existence of required sorted finite-graph patterns among the actual coding fibres.

## Lean acceptance

Formalize the basic contradiction via exact IsCodingNode old columns, HensonOneType.Extends, induced graph edge equality, and literal sourceCodingFibre prefix conditions. Derive the equal-target-level distinctness corollary. Strict targeted Lean and named transitive-axiom reports; no global BRD or multi-sort validation marker is promoted.

**Proof simplification discovered before Lean certification.** The second theorem's explicit assumption that target types have equal levels is unnecessary: if two target types were literally equal, their levels and exact old bits would already coincide, and the first contradiction would apply. Thus the Lean theorem proves distinctness *without* assuming equal target levels; the same-level use in the manuscript follows as a special case. This removes a dead hypothesis rather than strengthening any unverified graph-age assertion.
