# Track F — true target lex order of two split daughters and non-interleaving of old branches

22 November 2026, late evening. English proof and adversarial audit BEFORE Lean.

## The local split geometry still missing after code-order preservation

The manuscript's direct independent-history proof treats free splits separately from independent codes. For rank≤2, a fresh source pivot q is used to split one parent branch into two children, with old-bit 0 and 1 at the pivot. For rank3, a rank-drop construction gives a rank3 all-zero left child and rank2 right child. The source→target embedding need not preserve original enumeration, and the two actual target daughters are named by TARGET lex order after synchronization. To justify this naming, one must control the true first differing target bit and show that neither an older branch nor an unsplit survivor can interleave between the daughters.

This note proves the order-theoretic part for ANY genuinely selected target pivot, not the physical existence of that pivot.

## Precise left/right split statement

Let parent,left,right be genuine finite Henson target one-types over one actual target ordinary-edge table E (any ell, no symmetry needed). Suppose parent≤left and parent≤right in the COMPLETE chronological type preorder, and both daughters extend strictly beyond the parent level m=parent.level. Suppose

  m ∉ N(left),  m ∈ N(right).

Then lexBefore(left,right), using alphabet convention 0<1. Proof: for each b<m, the old positive/negative bits of BOTH daughters agree with parent (complete chronological extension). Hence they agree with each other at EVERY b<m. At b=m, by hypothesis left has 0 and right has 1, and m is inside both daughter domains. Therefore m is their FIRST differing bit. They are genuinely distinct, with left lex earlier than right. This does not assume source and target pivots have the same original index.

## Old branches cannot interleave with the daughters

Let otherOld be a genuine target branch that was already distinct from parent at the previous checkpoint. Let otherNew extend otherOld chronologically through the split construction. Suppose either lexBefore(otherOld,parent) or lexBefore(parent,otherOld) was known at the old checkpoint.

If otherOld<parent, the EXISTING first bit separating them is below both old levels and is preserved under otherOld≤otherNew, parent≤left, parent≤right. Apply the independently verified lex refinement lemma #498 twice to conclude

  otherNew < left and otherNew < right.

If parent<otherOld, the same argument gives

  left < otherNew and right < otherNew.

Consequently the daughters occupy one contiguous target lex block between the pre-existing old branches; no old surviving branch becomes interleaved between them. The final parent/daughter relation is local and does not require a global numerical raw-age equality.

## Adversarial audit

1. The split pivot m is the actual TARGET parent.level, NOT necessarily the SOURCE pivot q used in the physical source construction. Under a nonmonotone induced e their numerical original indices need not coincide.
2. The local bit assumption must be on genuine target daughter old-neighbour sets at exactly their common parent.level. Merely having source daughters with 0/1 at q does not imply this for target daughters; that physical target-meet identification remains unproved.
3. The two daughters must strictly extend beyond m so the new pivot bit is genuinely in their common domain.
4. Each daughter must chronologically extend the SAME genuine target parent, preserving both old 0 and old 1 bits; merely positive-neighbour inclusion would not prove they agree at all earlier b.
5. Relative lex ordering uses alphabet 0<1 and an actual FIRST differing bit. The all-zero branch remains to the left, consistent with the frozen manuscript's convention.
6. The daughters are automatically distinct from their opposite pivot bits, without a separate uniqueness axiom.
7. The old other branch's relative order is an explicit premise; if old branches share equal prefix and have no old first difference, this lemma does not invent an ordering.
8. The old other branch and the split parent may have distinct old levels in the abstract lemma; lexBefore explicitly supplies a genuinely shared old difference.
9. The otherNew type MUST extend the correct otherOld target branch, not an arbitrary type of equivalent age. Age or finite sorted-class equality is insufficient for chronological relative order.
10. The no-interleaving proof uses existing #498 genuine target lexBefore_of_extensions twice, not any source lex ordering or source embedding monotonicity.
11. The result covers every old unsplit branch individually, including a third branch in the independent triple case. It does not depend on the number of unrelated sorts.
12. The split parent may have old numerical singleton rank zero, one or two; rank is irrelevant to FIRST difference once the true target daughter bits at m are given.
13. Source rank-large fan existence and full K4 target synchronization have already been separately formalized, but this lemma does NOT claim they place the actual target daughter meet exactly at m or give the required 0/1 target pivot bits.
14. The manifold of mixed canonical supports, including triples, is not changed by a pure lex-order lemma; the required profile symmetry under swapping daughter labels remains a separate normalization issue.
15. The left/right daughter target type FIRST difference persists under all later genuine refinements, by #498.
16. The lemma does not prove full split-event history, absence of unrecorded age changes, dependent Kpt E/B3 records, any 24-orbit classification, or a BRD lower bound.
17. No frozen black manuscript proof text or global validation marker should be changed.
18. No new axiom or use of the published diary BRD characterization is required; each type is a true finite Henson one-type and lex order is defined directly by its old bits.

## Lean acceptance

Prove (A) two genuine parent extensions with opposite 0/1 bit at the actual parent pivot are STRICTLY lex ordered, (B) an old branch strictly to the left/right of the parent stays on that same side of BOTH daughters under genuine refinements, and (C) a combined no-old-branch-interleaving theorem. Use the checked target lex refinement API and exact real old-neighbour membership; dedicated exact-head Lean, strict named standard-only transitive axiom gate and full CI. The physical target meet/pivot location, complete split-age and diary iteration remain separate open obligations.
