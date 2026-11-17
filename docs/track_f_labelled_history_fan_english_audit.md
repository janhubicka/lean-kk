# Track F — labelled finite source-history fans (different old roots preserved)

17 November 2026. **English proof and hostile audit committed before Lean.** Extends the verified finite-history new-fan theorem #320 to source histories where the SAME previous finite one-type may be listed under DIFFERENT source roots, as happens when diary sorts are duplicated or source types are identified.

## Source data and statement

Fix a genuine actual chronological Henson one-type root `u` of zero-based rank n+1 and a set `S` which is (n+1)-large above u. Fix an ARBITRARY finite collection `old : Finset (Node × Node)` of PAIRS `(oldNode,oldRoot)`. The first component is a previously chosen actual finite TYPE node; the second component records its original source sort root. The same `oldNode` may appear with two different roots, and the distinct pairs must BOTH be controlled.

For any k, choose a finite fan G of k lower-rank daughter type nodes g≥u, each of rank n and carrying S n-largeness, pairwise incompatible and internally fresh-positive-marker-disjoint (all relative to u). In addition, for every pair `(a,r)` in `old` and every new g∈G, require

    (a.neighbours \ r.neighbours) ∩ (g.neighbours \ u.neighbours) = ∅.

The conclusion is an actual equality of finite old-positive marker sets, not an assertion about target embeddings or selected original coding vertices.

## Proof

Set H above both u.level and the level of the FIRST COMPONENT of EVERY pair in `old`; finiteness allows a maximum. Zero-pad the original u to H, preserving its exact old positives and negatives, rank n+1 and S-largeness. Apply the previously verified rank-large finite-fan theorem to obtain k rank-n, S-large daughters beyond this padding, with internal incompatible cones and pairwise fresh marker disjointness. Padding leaves u.neighbours unchanged.

Now let `(a,r)` be ANY previous pair. Every previous marker from a.neighbours\r.neighbours lies below a.level<H. Every new g extends zeroPad(u,H), so the new fresh marker set g.neighbours\u.neighbours contains NO vertex below H. Their intersection is empty by the already verified cross-root `fresh_markers_disjoint_of_later_zeroPad` lemma. Crucially r can vary independently for two distinct labels of the same previous node a.

## Hostile checks

1. Do not collapse the labelled set of old pairs to a Finset of old nodes and then choose one arbitrary root per node; the same old type can carry DIFFERENT fresh marker sets relative to different roots.
2. The new-family cross-disjointness uses the same u for all new daughters, but previous labels may have unrelated old roots and ranks.
3. Old pair entries must preserve their first component's finite level, not the second component root level, because the marker indices live below the old NODE's level.
4. Pairwise incompatible new cones are supplied by the previously verified finite-fan theorem, not by marker disjointness alone.
5. Internal marker disjointness initially refers to zeroPad u; it must be rewritten to the actual unpadded u neighbourhood before stating the final theorem.
6. No actual original coding node is manufactured in the conclusion. Every new daughter is a consistent type carrying a genuinely rank-large set S; actual coding witnesses come later via rank-largeness and the IsCodingNode restriction.
7. The proof uses only chronological prefix bit preservation, no Henson left-density, no induced target map, and no diary characterization.
8. Iterating this lemma for finite active front sorts still requires formal selection with proper labels and proofs of all mixed raw clique inequalities. The present lemma does not itself construct prescribed future edges between the daughter cones.

## Acceptance

Lean theorem with exact cardinality k, per-daughter rank/largeness, internal cone incompatibility, internal disjoint markers, and cross-disjointness for EACH PAIR `(oldNode,oldRoot)`; exact-head standard-only named axiom check. Frozen black TeX and full BRD/global diary marks stay pending.