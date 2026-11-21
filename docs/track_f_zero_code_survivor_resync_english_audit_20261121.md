# Track F — resynchronize all surviving K4 fibres after a selected zero-code original

21 November 2026. **English proof and adversarial audit before Lean.** Complements the physical code-vertex selection in merged lean-kk PR #424 and the complete tuple synchronization verified in merged PR #410.

## Goal

Suppose `u_i, i∈Fin(d)` are pairwise distinct **genuine source K4 Henson one-types** at one old source level m, and each assigned genuine target type `v_i` is actually rank-compatible with it: target/source singleton ranks agree and the sourceCodingFibre(Etgt,e,v_i) is recursively rank-large above u_i. The target is genuinely K4-free, and `e` is an injective induced map of the two-direction ordinary edge tables, NOT assumed enumeration-preserving.

Let **r≥m** be an already chosen source original index (the code to be deleted from the active front), with its genuine target image e(r). Take any target cutoff B.

We construct genuine source refinements `w_i` all at one common source level M and target refinements `t_i` all at one common target level H>B and H>e(r), such that:

1. All original source and target types extend to w_i,t_i; source/target singleton ranks and actual coding-fibre largeness are preserved.
2. The new target types are pairwise distinct.
3. **Every survivor target type has zero bit at the ACTUAL selected target original e(r)**. Thus all of its later actual coding descendants are nonadjacent to e(r), in BOTH orientations. The source w_i likewise has zero bit at r, hence all its actual coding descendants avoid r.
4. Every nonempty original-source raw support bound is unchanged, including mixed triples. The complete canonical finite sorted-graph classes of the original surviving source tuple and new target tuple coincide, uniformly for all finite symmetric K4-free B and repeated sort labels.

This is the geometric survivor step in the independent-code case. It is **not** the entire code event: no assertion is made about the last selected j-branch's precode target profile or the chronological record immediately around e(r).

## Proof

**Zero-pad all survivor source roots.** Since m≤r and every positive neighbour of u_i is <m, the exact zero-pad z_i=zeroPad(u_i,r+1) has neighbour set literally equal to u_i.neighbours, rank unchanged and **r∉z_i.neighbours**. It lies above the source original r at common level r+1. The verified rank-large cone monotonicity makes the SAME actual target coding fibre of v_i rank-large above z_i. The z_i are pairwise distinct: equality of z_i,z_j would imply equality of their finite old positive-neighbour sets, hence equality of the original same-level genuine u_i,u_j (verified field extensionality, PR #407), contradicting original injectivity.

The old and z raw support profiles coincide on EVERY nonempty support: no new positive marker was introduced, all ranks remain equal, and the private-marker condition holds vacuously. Apply the verified PR #400 raw profile preservation theorem (the prefix itself grew, but nonempty common-neighbour pools are still entirely below m).

**Resynchronize after the code.** Pick one target cutoff

`C = max(B+1, e(r)+1, 1+max{e(a):a<m})`.

Everything is finite. Apply the merged verified full K4 tuple synchronization PR #410 to the genuinely compatible common-level **padded** source tuple z_i and the original target tuple v_i with bound C. It produces w_i,t_i at common levels M,H with H≥C, retains actual fibre largeness and rank, and forces target types distinct. (PR #410 itself also ensures H includes images of every source coordinate below r+1; we need only the explicitly chosen C to transport the ORIGINAL old neighbours.) Its complete source raw equality, together with u→z equality, gives the original u→w raw profile equality on every nonempty support.

**Show the actual target zero passing bit at e(r).** Fix i. We know z_i≤w_i, r<z_i.level=r+1≤w_i.level and r∉z_i.neighbours. The complete chronological extension preserves the **negative** bit r, so r∉w_i.neighbours. The rank-large ACTUAL target fibre at t_i above w_i contains a GENUINE coding node x_i with w_i≤x_i. Therefore r<x_i.level and the full two-direction actual source coding columns satisfy

`E_s(r,x_i.level)=E_s(x_i.level,r)=false`.

Inducedness transports both bits to the true target image pair (e(r),e(x_i.level)). Since H≥e(r)+1, the old target index e(r) is below t_i.level=H. The sourceCodingFibre(t_i) predicate says the target pair columns equal decide(e(r)∈t_i.neighbours). The transported value is false, hence **e(r)∉t_i.neighbours**. Consequently *every* actual later target-fibre vertex in t_i also has both target edges to e(r) equal false (the fibre's definition fixes these old bits). No symmetry assumption beyond explicit two-direction inducedness is needed in the proof.

**Complete canonical class comparison.** The rank-large refined source fibres, original u→w full raw source equality and target level H beyond images of ALL original positive source neighbours discharge the old/new separate hypotheses of the verified original/refined sandwich theorem PR #399. Its canonical full-support version gives precisely the same finite K4 graph class for original u and new t, uniformly over every finite symmetric K4-free abstract B and arbitrary sort map. Numerical equality of redundant target raw bounds is **not** asserted.

## Adversarial audit

1. r≥m is essential to make every survivor zero pad set bit r to zero without erasing a previously fixed positive neighbour.
2. The selected coded source original r is assumed GIVEN here. PR #424 constructs it later than any target cutoff from a rank-zero actual coded fibre; do not conflate the two distinct lemmas.
3. The original survivor source roots must be distinct at common m, because the tuple synchronization theorem #410 requires an injective old root map. Padding to r+1 preserves distinctness via genuine finite-type extensionality.
4. The original assigned target types v_i may coincide and have different levels. #410 explicitly permits this.
5. All source rank equality statements come from exact zero padding and #410; do NOT infer target rank equality from a mere nonempty target fibre.
6. The same ACTUAL target coding-node sets remain large after source zero padding by verified cone-monotonicity. No new target type is invented during padding.
7. Need H **strictly above** e(r), not merely H≥e(r), to read the target bit at e(r) as an old prefix bit.
8. The finite target cutoff also exceeds images of ALL source old coordinates a<m, not just r. The embedding e can send old neighbours very far in target order.
9. The source-to-target embedding is injective and induced on off-diagonal ordered pairs. Here r<x_i.level ensures the source pair is genuinely off diagonal.
10. Both graph orientations are false by IsCodingNode and inducedness. Target sourceCodingFibre stores both directed target old columns.
11. Negative-bit preservation along z_i≤w_i≤x_i is required. Mere positive-neighbour inclusion would NOT establish the zero bit at r.
12. The survivor target types t_i are pairwise distinct but need not preserve the original source sort or lexicographic order. Actual history realization must use the **target** order.
13. The source raw full-support equality is literal on all nonempty supports, including support triples; zero padding is not allowed to rely on the empty support ([0,m) grows).
14. The target numerical RAW profile may differ on redundant supports. The conclusion is complete finite sorted-class/canonical-test equivalence, not pointwise raw-number equality.
15. For d=0 all target and source survivor conditions are vacuous, and the conclusion still makes sense; no Fin(0) element may be selected.
16. The rank-large extraction of x_i is used only as a witness to read the target old bit e(r); it does not change the synchronized front.
17. A later coding-node descendant in t_i sees e(r) with bit zero by the **target fibre's full old-column predicate**, not because its target enumeration position is ordered similarly to source.
18. Even with this result, to prove the exact code event one must compare the **actual precode profile at e(r)** and the immediate survivor post-code profile, using integer-age monotonicity and legal zero-code law (draft PR #430), plus the no-hidden-events sandwich.
19. The lemma does not realize cover or split events, full Kpt L+/E diaries, or any big Ramsey count.
20. Frozen black manuscript text and global history-realization validation marker must remain unchanged until full end-to-end proof is checked.

## Lean acceptance

Formalize two named pieces: (A) a large ACTUAL source coding fibre with source-zero bit at r and a target prefix beyond e(r) forces target type bit zero at e(r); (B) the finite-survivor construction using exact source zero padding and the verified #410 tuple theorem, reporting source/target rank/large invariants, target injectivity, target zero bit at e(r), exact all-support raw source equality, and universal canonical finite sorted-class equivalence. Dedicated exact-head Lake build and strict standard-only axiom gate before merging. Do not modify frozen prose.
