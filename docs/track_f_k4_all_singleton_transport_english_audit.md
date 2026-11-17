# Track F — complete one-coordinate compatible rank transport for K4 Henson types

17 November 2026. English proof / adversarial audit **BEFORE Lean**. The target is the entire singleton-rank version of the olive `lem:independent_lower_transport`, NOT the full multi-sort synchronization or direct independent-set BRDs.

## Setting

Fix ell=4 and actual source/target ordinary graph tables Esrc,Etgt; Etgt avoids the normalized K4 Henson forbidden family. Let e:Nat→Nat be injective and induced (not assumed enumeration-order preserving). Let v0 be any target HensonOneType 4 and u any consistent source HensonOneType 4. Assume that the EXACT ACTUAL sourceCodingFibre(Etgt,e,v0) is recursively rank(u)-large above u.

## All possible singleton ranks

By its actual finite graph-capacity definition, the zero-based Lean source singleton rank is `4-1-cap_Esrc(u.neighbours)-1`. This is a natural number between 0 and 2. In manuscript one-based units these are exactly singleton ranks 1,2,3. No other one-coordinate rank can occur.

## The SAME-RANK continuation theorem

For every target cutoff B, find a genuine target type vH≥v0 and source type uH≥u such that vH.level≥B, rank(uH)=rank(vH)=rank(u), and the ACTUAL coding-node sourceCodingFibre(vH) remains rank(u)-large above uH.

Proof by the three actual possible ranks:

- Lean rank0 (manuscript rank1): use already verified `sourceCodingFibre_continue_equal_rank_zero` (merged PR #301), which needs no source clique richness.
- Lean rank1 (manuscript rank2): use verified `sourceCodingFibre_continue_equal_rank_one` (merged PR #302), whose reverse target-rank bound comes from a genuine source edge in the selected rank1-large coding fibre.
- Lean rank2 (manuscript rank3): use new `sourceCodingFibre_continue_equal_rank_two` (draft PR #311, exact-head GATE PENDING at time of this note). Its reverse bound uses the now-verified source triangle-richness theorem (#307) and all-size source-fibre clique transport (#310).

Each theorem carries precisely the same source coding-node fibre and the same target normalized-Henson/induced-embedding hypotheses. The finite case distinction is legitimate because the actual rank is bounded by 2, not an arbitrary diary age.

## The universal POSITIVE-RANK DROP theorem

Assume additionally 0<rank(u). For every B, find source uH≥u and target vH≥v0 with vH.level≥B, both exact rank(u)-1, and actual fibre(vH) rank(u)-1-large above uH.

Proof: write rank(u)=n+1. Apply the DEFINING successor clause of `RankLargeness.Large` at the source root u, producing a descendant w≥u of exact rank n and actual sourceCodingFibre(v0) n-large at w. Apply the already proved full K4 SAME-RANK continuation theorem to w at cutoff B. The returned types have both rank n and the new actual source fibre remains n-large. Transitivity yields u≤uH. This uniformly subsumes the already verified special drops #303 (rank1→0) and #306 (rank2→1), and makes the rank-drop half of the olive proof a one-line induction consequence.

## Hostile audit

1. The theorem applies to actual `HensonOneType 4` neighbourhoods with *explicit* K3-freeness certificate, not diary rank labels from Definition 3.1.
2. Zero-based vs one-based rank is explicit; Lean rank2 corresponds to manuscript singleton rank3, not rank2.
3. The case split covers all possibilities because the definition is bounded by 2 for ell=4. Do not infer bound from a general ell without additional argument.
4. Each same-rank component applies to the ACTUAL coding-node source fibre, not the entire hypothetical type tree.
5. e must be an injective INDUCED graph embedding; none of the component theorems assumes it preserves enumerations.
6. Target normalized K4 avoidance remains explicit and is needed for the physical target-type and future clique arguments.
7. The universal drop does NOT require the original target type rank equal source rank as an input; it needs only an already large exact source coding fibre. The requested conclusion has both NEW ranks matching one lower.
8. The source lower-rank descendant w from the recursive definition may be hypothetical; source fibres still consist only of actual coding-node extensions.
9. No extra isolated-neighbour certificate is constructed in the drop theorem. Repeating that old proof would introduce unnecessary mixed-old-clique assumptions.
10. Even if both theorems are Lean verified, this settles only the **SINGLETON one-type** source/target rank transport, not compatible tuples of multiple types, complete profile F, diary-envelope persistence or global BRD exactness.

## Acceptance

Wait for PR #311's exact-head rank2 SAME-RANK theorem and strict axioms to pass and merge, then formalize K4 case split and universal positive-rank drop with standard-only named Lean axiom gates. Keep black text untouched and the manuscript's *full* `lem:independent_lower_transport` marker pending until its multi-sort use/assumptions are audited.