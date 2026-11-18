# Track F — conditional equality of complete finite source/target extension classes

18 November 2026. English proof and adversarial audit, written **before** Lean.

## Statement

Let \(E_s,E_t\) be genuine chronological source and target graph tables, with \(E_t\) \(K_\ell\)-free. Let \(e:\mathbb N\to\mathbb N\) be an injective induced embedding, with no order-preservation assumed. Let \(u_i\) be genuine source types at common source level \(m\), and \(v_i\) genuine target types at common target level \(H\), with an arbitrary finite sort family \(\mathrm{Fin}(d)\).

Assume:
1. Each **actual** source coding-node fibre of \(v_i\) is rank-large at the genuine rank of \(u_i\), above \(u_i\).
2. For every old source positive neighbour \(c\in N(u_i)\), its target image \(e(c)\) lies below \(H\).
3. The target edge table is genuinely \(K_\ell\)-free, and \(e\) preserves BOTH directed off-diagonal edge bits.

Then, for **every** finite symmetric graph \(B\) on \([0,N)\) with arbitrary possibly-repeated original source sort map \(\sigma\), the finite source RAW clique feasibility condition for **every nonempty** clique \(C\) of \(B\) is logically **equivalent** to the finite target RAW clique feasibility condition for the same \(B,\sigma,C\).

Equivalently the complete finite sorted graph extension classes of the source and target tuple are the same, conditional on the listed hypotheses. This avoids claiming pointwise equality of redundant raw numerical bounds; equality of canonical profiles can be derived later from the verified canonicalization theorem as a separate application.

## Proof

**Source feasible ⇒ target feasible.** The newly merged exact-head [PR #380](https://github.com/janhubicka/lean-kk/pull/380), \`trackFAllRanks_source_feasible_implies_target_feasible\`, already proves the implication by using full source finite richness and transporting ACTUAL source cliques into the target. It needs no old-image cutoff beyond the target fibre definition. Every nonempty clique support of \(B\) is transported.

**Target feasible ⇒ source feasible.** Fix a nonempty directed clique \(C\subseteq[0,N)\). Its label image \(S=\sigma[C]\) is a nonempty finite support even when labels repeat. The independently verified physical upper-bound theorem \`trackFCommonRawAge_target_le_source_of_large_fibres\` (PRs #332 and the merged all-support application) applies to the genuine common-neighbour pools on \(S\): because each old positive source neighbour has its image in \(N(v_i)\), inducedness preserves every old source common-neighbour clique. Therefore
\[
 \operatorname{RawAge}^{E_t}_{H}(S;(v_i)_i)
 \le \operatorname{RawAge}^{E_s}_{m}(S;(u_i)_i).
\]
Composing this inequality with \(|C|\le\operatorname{RawAge}^{E_t}_{H}(S)\) gives source feasibility for \(C\). Since \(C\) was arbitrary, the reverse implication holds.

## Adversarial audit

- The two directions use genuinely different ingredients. The inclusion source→target depends on actual **joint finite source realization** (#367/#380); the reverse target→source needs only transported old source cliques and is numerical on every nonempty support.
- The theorem **does not assume** numerical raw-age equality; a raw support inequality can be redundant in the finite graph class even when its numerical value changes.
- The additional old-image-cutoff hypothesis is explicit, and is geometrically achievable by taking \(H\) beyond finitely many images. However, establishing rank-largeness simultaneously *at that \(H\)* while preserving all original source supports is a **separate** problem.
- No equality of source and target singleton ranks is needed as an independent hypothesis: the two finite-class inclusions already impose all singleton feasible patterns. But geometric construction of the compatible fibres still needs rank bookkeeping.
- No injectivity of \(\sigma\) and no order preservation of \(e\) are required. The finite graph \(B\) is required to be symmetric as in the verified source-realization theorem.
- The conclusion is logically \`(∀ C, sourceRawCondition C) ↔ (∀ C, targetRawCondition C)\`. This is the precise finite-class equality rather than an abstract diary identity.
- Empty \(B\) is handled vacuously. We require nonempty cliques to apply the target nonempty-support upper bound; the image of a nonempty clique under a total \(\sigma\) is nonempty.
- No use of the disputed diary characterization or the published exact BRD counts occurs.
- Manuscript implication: the black synchronization proof currently introduces a separate old certificate clique on each support. The conditional **finite-class equality** can instead be derived from the two physical inclusion theorems, removing that particular certificate construction once the geometric simultaneous-fibre step is supplied. Since black text is frozen, record this as a separate optional simplification, not an unverified textual replacement.

## Validation criterion

Exact-head Lean build + strict one-theorem standard-only axiom report for the equivalence. Until then this is an English proof. The global diary persistence and BRD lower-bound validation marks remain pending.