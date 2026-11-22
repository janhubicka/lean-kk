# Track F — extract the TRUE target meeting pivot of two synchronized distinct daughters

22 November 2026, late evening. English mathematical proof, with hostile audit, BEFORE Lean.

## Why this is the correct next split lemma

The manuscript's lower-bound split construction chooses a fresh SOURCE original q and two rank-large source daughter fibres with opposite source bits at q. Under an arbitrary induced embedding e, the TARGET image e(q) need not be the first differing TARGET coordinate of the final synchronized daughter prefixes. The frozen proof explicitly names daughters in their TRUE TARGET lex order. The newly kernel-checked conditional target split pivot theorem (Track F PR #505) ordered daughters from a GIVEN target common-parent pivot where their 0/1 bits are known. We now REMOVE that extra target pivot hypothesis: from genuine distinct target daughters extending one target parent, the ACTUAL first-difference pivot exists automatically.

## Precise theorem

Let parent, a, b be TRUE finite Henson one-types of the SAME actual target graph E, any ell. Suppose parent≤a and parent≤b in the complete chronological type preorder; a and b have the SAME genuine later level H; and a≠b as real types. No assumption that e or source chronology preserves target order.

Then there exists a TRUE target coordinate L such that

  parent.level ≤ L < H;
  for every x<L, (x∈N(a)) ↔ (x∈N(b));
  exactly one of L∈N(a), L∈N(b) holds.

This L is the FIRST differing target bit (the exact target meet level), not merely an arbitrary separator. Consequently either a<lex b (if bit a=0,b=1) or b<lex a (if bit b=0,a=1); naming them left/right by actual TARGET lex order produces a genuine 0/1 target pivot at L, and the two old parent prefixes agree through every earlier coordinate. No source–target chronological-order hypothesis is required.

## English proof

1. The complete actual Henson one-type has only level and positive-neighbour-set data, with proof fields irrelevant. Since a and b have the same level H but are distinct, genuine type extensionality (#407) implies N(a)≠N(b).
2. Both N(a), N(b) are subsets of [0,H) by their genuine below fields. Therefore there exists x<H with exactly one membership. Otherwise finite-set extensionality would make N(a)=N(b).
3. Among all such x choose the LEAST natural L (well-ordering of Nat). This choice belongs to [0,H), and for every x<L the membership bits agree. The proof can use Nat.find on the property x<H ∧ ¬(membership equivalence).
4. The shared old parent means every x<parent.level has the same bit in both daughters, since complete chronological extensions preserve old positive AND negative bits. Thus the first differing L must satisfy parent.level≤L.
5. The opposite membership at L gives two possible orientations. If a has bit0,b bit1, then lexBefore a b is witnessed by L and the exact smaller-bit agreement; otherwise lexBefore b a is witnessed by L. Both daughters are automatically distinct.
6. Once each actual target first-difference is identified, the previously checked #505 theorem ensures every other OLD branch which lay left/right of the common parent remains left/right of BOTH daughters. Hence no unrelated old branch interleaves between them in the ACTUAL target sorted order.

## Hostile audit

1. The theorem requires ACTUAL SAME TARGET LEVEL H for a,b. Without it, different lengths can have different types but no differing bit before both domains.
2. A genuine common old parent is essential for the lower bound L≥parent.level. If daughters merely share some arbitrary age profile, there may be a differing old target bit.
3. The first-difference L is in the **TARGET** numerical enumeration; it need not equal the SOURCE pivot q or its image e(q), and we make no such assertion.
4. The direction of lex order is determined by TARGET bit 0<1. The names "left" and "right" should be chosen AFTER inspecting actual target first bit, not copied from source labels.
5. An arbitrary separating target bit is insufficient to prove the first meet level; minimality is needed to force all earlier bits equal.
6. The two actual Henson types have finite positive-neighbour sets and explicit below fields, so the finite-level extensionality and Nat.find well-ordering are legitimate.
7. Every negative old bit must be preserved by parent≤daughter; mere positive-neighbour inclusion cannot establish equality at all older coordinates.
8. d=0/1 does not enter this two-type theorem; application to two freshly duplicated daughters requires two actual distinct sorts.
9. The target synchronization result #410 provides same-level and target injectivity when distinct SOURCE daughters and individually compatible coding fibres have been constructed; this first-difference lemma then applies without additional target pivot assumptions.
10. No source/target index-order-preserving embedding is assumed. No claim is made that the source parent rank or its age identifies the target first-difference position.
11. If the daughters' first difference occurs after several numerical gaps, these gaps are simply ignored in the diary record, consistent with manuscript conventions.
12. The old unsplit other branches remain separate by earlier target old differences; checked #505's non-interleaving ordering is conditional on their old lex relation and true refinements, not on RAW-age equality.
13. This proves a real combinatorial target meet pivot, but does not force the target singleton rank decrease or the complete post-split age profile. Those require actual source-fibre/age sandwich arguments.
14. The claim is pure finite Henson target-type geometry and works for any ell,E, with no forbidden family or left density hypothesis beyond the genuine safe type constructors.
15. The first difference is uniquely least by Nat order, though theorem need not assert uniqueness separately: the stronger all-earlier-bit-equality statement already fixes it.
16. This does not prove the actual split construction from a given prescribed diary history, nor full dependent Kpt E/parameter/B3 data, 24-case diary count or global BRD lower bound.
17. It does not conclude the source daughter labels match target left/right. The correct TARGET reindexing/permutation after a split remains to be carried explicitly through the complete canonical profile.
18. The frozen black manuscript proof is never edited; only precise validation TODO notes may be added after strict exact-head Lean checks.
19. The outcome must be tested for BOTH orientations, not one; otherwise it would silently assume target lex order of the initial two source-labelled daughter coordinates.
20. The code must not introduce an axiom, sorry or unproved bridge from target rank to source original order.

## Lean acceptance

(A) Extract least true target first-difference coordinate L with parent.level≤L<H and all earlier old bits equal.
(B) Prove target lex dichotomy a<lex b or b<lex a from the exact first-difference bits.
(C) Optional strengthened local no-old-branch-interleaving corollary via verified #505 and old-branch extension.
Run exact-head dedicated Lake build, strict named standard-only transitive axiom reports and full CI before merging.
