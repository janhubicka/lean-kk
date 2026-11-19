# Track F — original/refined source-type sandwich for conditional target age equality

19 November 2026. English proof FIRST, with adversarial scope audit. Follows exact-head verified and merged PRs #380, #383 and #395.

## The refinement/cutoff conflict

The existing conditional finite source/target class equivalence #383 uses the SAME source family u_i in two roles: (a) rank-large coding fibres for finite source richness and (b) original old-neighbour images lying below the target cutoff H, to bound the target raw ages above by the source raw ages. In a sequential front synchronization, each source root may be refined to u_i^new after H is selected. The finite image of new positive-neighbour markers is NOT necessarily below H because e is an arbitrary injective induced self-embedding, not order preserving. Thus applying #383 to the refined roots would tacitly require a new cutoff and may create a circular argument.

## Correct two-root hypotheses

Take finite source families old_i at common source level m and new_i at common larger source level M, both genuine actual Henson one-types for the same source graph. Assume old_i ≤ new_i for every i (full positive AND negative old-bit agreement). Take genuine target types v_i at a common target level H, with arbitrary injective induced e:E_source→E_target and target forbidden-family avoidance.

Assume: (i) each ACTUAL coding-node target fibre of v_i is rank-large above new_i at its actual rank, (ii) H exceeds the image e(c) of each OLD positive neighbour c∈N(old_i), and (iii) the exact original and refined source RAW finite support functions agree on all nonempty sort supports. Importantly, **do not** assume any image bound for the newly introduced neighbours of new_i.

## Lemma: target raw bound ≤ original raw bound

Fix an i. A nonempty rank-large actual target coding-node fibre at new_i contains an actual coding node x extending new_i. Since old_i ≤ new_i, transitivity gives old_i ≤ x. The existing verified old_source_neighbour_images_in_target lemma, using only the cutoff H for N(old_i), implies

    e[N(old_i)] ⊆ N(v_i).

All target old neighbour sets lie below H because each genuine v_i has level H. Fix any NONEMPTY support S. The image of the source common-old-neighbour pool for old_i, i∈S, therefore lies in the target common-old-neighbour pool; nonemptiness of S ensures it lies BELOW H even though e need not preserve order. Injective inducedness preserves finite directed clique capacity of the image. Pool inclusion gives cap(target-common(S))≥cap(source-old-common(S)); hence

    RAW_target_H(S) ≤ RAW_source_old_m(S).

This lemma does not need the raw-profile equality old↔new; it only needs new large coding fibres, old≤new and cutoff for old positive neighbours.

## Corollary: conditional equality of finite sorted-graph extension classes

For every finite symmetric labelled graph B with potentially repeated sort labels σ:

**Source-old exact feasibility ⇒ target exact feasibility.** Apply hypothesized RAW_source_old(S)=RAW_source_new(S) on the exact support S=σ[C] of each nonempty B-clique C. Thus B is new-source feasible. Apply merged verified Track F source→target transfer #380 with the rank-large ACTUAL target coding-node fibres at new_i to obtain target feasibility.

**Target exact feasibility ⇒ source-old exact feasibility.** For each nonempty B-clique C, use its nonempty label image S and the just-proved target≤old upper bound: |C|≤RAW_target_H(S)≤RAW_source_old_m(S).

The result is a complete iff for finite sorted B. No bound on e[N(new_i)] is used anywhere.

## Corollary: complete canonical age-test equivalence

If B is additionally K_ell-free on the finite vertex domain [0,N), the verified Track F exact↔full support lemma #395 converts the above exact-support iff into a full-support iff. The existing normalized integer canonicalizer preserves all-support clique-vector feasibility for each of the two raw profiles, yielding equivalence of the **complete canonical finite-graph acceptance tests** using original source and target types.

No numerical equality of their raw or canonical age tables is asserted, and no new source/target front is constructed.

## Adversarial audit

1. **Crucial old/new asymmetry:** we require rank-largeness of actual coding fibres above NEW roots, but the target image cutoff only for OLD positive-neighbour sets. Never apply old-image transport to NEW roots.
2. **Only actual coding nodes:** abstract hypothetical extension nodes do not suffice to deduce E_source(c,x.level) or target fibre columns.
3. **Preorder direction:** old_i≤new_i≤x; do not reverse inequalities or assume large(new)⇒large(old). That implication is false in general.
4. **Cutoff timing:** the final M/source positive markers may have target images above H. This is allowed and expected under a nonmonotone e.
5. **Directed inducedness:** preserve off-diagonal edge bits in the required old→coding direction; the existing verified physical lemma supplies image inclusion.
6. **Arbitrary repeated sort labels:** one root per sort, any B labels may repeat. Large(source_new_i) realizes all finite source-feasible B with repetition (verified #367).
7. **Nonempty support:** e does not necessarily send the source [0,m) prefix inside target [0,H); for empty support no cross-ambient upper bound is claimed.
8. **Target H nonempty:** old v_i neighbours are below H by the genuine one-type property, not an extra geometric assumption.
9. **Raw profile equality is a separate premise:** it must be constructed from singleton rank preservation and disjoint fresh positive markers in the pending tuple synchronization. Do NOT silently infer it from old≤new or same-rank individual continuation alone.
10. **Source ranks may vary; no label injection or target order preservation is assumed.**
11. **B symmetry** is passed to verified source-richness; canonical variant requires the separate finite B K_ell-free check for correct bounded integer-age supports.
12. **Old source type common level m and new common level M** are required by the finite source-richness and raw-support formulas; not implied by componentwise extension alone.
13. **No numerical raw equality across target:** target raw supports can be redundant, even when complete finite graph classes agree.
14. **No target tuple construction:** v_i and large fibres are explicit inputs, not outputs. Distinctness of target v_i is neither inferred nor required for the conditional result.
15. **No Kpt E/B3 claim** and no occurrence of a concrete diary in every subcopy.
16. **No exact big Ramsey lower bound:** all black manuscript synchronization, diary persistence and BRD markers remain pending.
17. **Canonical tests include empty cliques and unused labels** through #395, but only for B that is K_ell-free.
18. **Do not force all new markers below H** in future Lean applications; that reintroduces the very circularity this bridge removes.

## Validation gates

Formalize three named endpoints: refined coding fibres imply OLD source-image transport and all-support target≤old upper bound; original↔target exact finite-class equivalence under separately hypothesized source old/new raw equality; canonical full-support equivalence on finite K_ell-free B. Dedicated exact-head Lean and strict standard-only axiom checks. Freeze manuscript black prose; note conditional scope only. Keep draft until green.