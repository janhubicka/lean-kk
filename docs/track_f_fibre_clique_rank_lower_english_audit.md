# Track F — any genuine source-fibre clique forces target singleton rank

17 November 2026. English proof and adversarial audit **before Lean**. This extracts a reusable all-sizes target-rank inequality from the verified actual target future clique bound (#275) and the exact sourceCodingFibre predicate (#285). The existence of a source clique remains an EXPLICIT separate premise; no diary or global BRD theorem is assumed.

## Theorem

Let Esrc,Etgt be actual original graph edge tables. Assume the target avoids the normalized forbidden K_ell family (so actual K_ell-freeness and symmetry hold), and e:Nat→Nat is an injective INDUCED graph embedding, with no chronological monotonicity assumption.

Fix a target finite type v. Let C be a FINITE set of original source indices which form a complete directed clique in Esrc. Assume for each c∈C that there exists a genuine finite source coding-node type t_c of level c and t_c∈sourceCodingFibre(Etgt,e,v). This is the precise actual source-fibre membership condition.

Then |C| ≤ ell-1-cap_Etgt(v.neighbours), the manuscript singleton rank of the target type v. Equivalently, if C contains at least n+1 vertices, its zero-based Lean target singleton rank is at least n.

## Proof

Take the actual target original-index set W=e[C]. Injectivity gives |W|=|C|, without requiring e preserve the ordering of C. The induced embedding carries all off-diagonal directed source edges of C to target edges, so W is a complete directed clique.

For each target original w=e(c)∈W, choose the ACTUAL source coding type t_c∈sourceCodingFibre(v). The fibre definition ensures w≥v.level. Moreover every p∈v.neighbours has p<v.level and both target edge columns satisfy Etgt(p,w)=Etgt(w,p)=1, because the target-prefix columns of t_c match v and p is a positive old neighbour. Hence W lies entirely in the target FUTURE cone and is completely joined, in both directions, to v.neighbours.

Invoke the already verified physical target-rank future-clique inequality (#275): |W|≤ell-1-cap(v.neighbours). This yields the claim.

## Hostile checks

1. The image set W is e[C], so its cardinality is |C| only if e is injective on C. We assume global injectivity.
2. The source set C must be a DIRECTED clique, not merely a finite set with sufficiently many original vertices.
3. Every source c∈C must be the LEVEL of an ACTUAL source coding node in the specific fibre. A hypothetical type or a source type outside the fibre gives no target-future or old-column information.
4. The embedding must preserve off-diagonal true edges in each orientation; injectivity alone is insufficient.
5. The actual target fibre guarantees the image w lies beyond v.level, not that e respects source order.
6. Every old target p∈v.neighbours is joined to EVERY image w; use the two-column fibre equations and p<v.level.
7. This proves target rank LOWER bound given a source clique; it does not create C from abstract rank largeness. Genuine source clique-richness is a separate theorem and remains the bottleneck at manuscript rank3.
8. The target normalized forbidden-family hypothesis is needed for the physical clique bound, not for the source image/fibre set algebra.
9. No mixed graph-age profile equality, diary history persistence, or exact degree count is concluded.

## Lean plan

Implement image clique transport on C, full old-neighbour join from actual sourceCodingFibre witnesses, and direct application of henson_targetRank_ge_futureClique. Then add a zero-based rank lower-bound corollary. Exact-head targeted Lean build and strict named standard-axiom reports, no black manuscript edits or global validation promotions.