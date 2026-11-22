# Track F — strengthen the checked actual zero-code theorem with real pre→post chronology and target lex order

22 November 2026, late evening. Adversarial English proof BEFORE any Lean edit.

## Why the previously kernel-checked theorem needs a stronger output

The completed ordinary-L zero-code theorem (merged PR #500) genuinely constructs pre-code survivor types at target level c=e(r) and immediate post-code survivor types at target level c+1, both by restricting the SAME later target one-types. Yet its **public conclusion** only says that pre(f(i))≤t_i, post_i≤t_i and their COMPLETE canonical sorted-graph ages agree. Two unrelated types can have the same canonical age while disagreeing on an old bit. Thus its public statement did not prove the sequential chronological fact essential to iterate the ACTUAL diary:

    pre(f(i)) ≤ post_i ≤ t_i

and it did not state that pre(f(i)) and post_i have EXACTLY the same positive old-neighbour sets (the code coordinate c is a ZERO bit for every survivor).

This interface needs an explicit repair. It cannot be obtained merely by comparing canonical ages, nor can it be asserted about arbitrary refinements with a shared final extension unless a code zero bit is known.

## The genuine physical proof

In the already verified proof of k4_full_actual_zero_code_ordinary_age_step, the true pre-code front is constructed by k4_precode_from_genuine_surviving_target_front (#492). The latter provides for EVERY survivor i:

    (pre(f i)).neighbours =
      (restrictPrefix (t i) (c+1)).neighbours.

The verified full code step then DEFINES

    post_i := restrictPrefix(t_i,c+1).

Therefore the positive-neighbour sets N(pre(f i)) and N(post_i) are literally equal. The genuine type levels are respectively c and c+1, so pre(f i)≤post_i follows from the FULL chronological Henson order: for each old coordinate a<c, membership on both sides is equivalent. The later post_i≤t_i is already verified by the exact prefix restriction lemma.

Thus a strengthened public conclusion can return, alongside all original outputs:

    forall i, pre(f i) ≤ post_i
       AND pre(f i).neighbours = post_i.neighbours.

This is stronger than class equality, explicitly preserves complete positive/negative old bits, and holds even when the source→target original-index map e is non-order-preserving.

## Consequence: target lexicographic invariants are inherited by every stage

The independent verified binary TARGET lex-order theorem (#498) defines lexBefore by the FIRST old-bit difference with alphabet 0<1 and proves invariance under true type extension.

Assume the original target front v:Fin(d+1) is in **true target lexicographic order**. The full ordinary-L code-step already returns v_i≤pre_i, v_{f(i)}≤t_i, and the strengthened result pre(f i)≤post_i.

Therefore:

* the full genuine pre-code target front pre remains lex sorted on Fin(d+1), because every v_i extends to pre_i;
* the immediate survivor front post on Fin(d) remains lex sorted because v_{f(i)}≤pre(f i)≤post_i and f=Fin.succAboveEmb j is strictly monotone;
* the later synchronized survivor front t on Fin(d) remains lex sorted because v_{f(i)}≤t_i and the same f is strictly monotone.

This uses ONLY target old bits, not guessed source lex labels. The target code branch j is actually removed; there is no future coded dummy in the public theorem.

## Hostile audit

1. The already verified age equality on survivor supports alone does NOT imply literal bit equality or chronological extension. We must use the **construction data** in the proof of #500.
2. Pre-code survivors are types of level c; post-code survivors have level c+1. Their neighbour sets can be equal only because every survivor's genuine target bit at c was proved zero (#433).
3. Positive-neighbour equality implies negative-bit equality on *old* prefix positions because these are complete bit vectors, so it is legitimate to construct pre≤post.
4. The same later target type t_i supplies both restrictions; choosing a different compatible representative with the same age would not suffice.
5. The lex proof uses the **actual target** old front already sorted by target order. It does not assume the arbitrary induced source→target map e preserves source order or source lex order.
6. Fin.succAboveEmb j is order-preserving and injective, and denotes deletion of exactly the selected **target** code sort, not source sorted deletion.
7. Initial v types need to be lex-sorted for the corollary. Injectivity or same rank alone is insufficient to infer a chosen indexing is lex-sorted.
8. The coded type j terminates after its genuine pre-code prefix; no post type at j exists or is introduced by this corollary.
9. The source past may be empty; all previous actual zero-edge constraints continue unchanged.
10. No new assumption on redundant raw support bounds, singleton ranks, large coding fibres, or finite graph class equivalence is introduced by the strengthening.
11. New conclusion must retain ALL original theorem outputs, including the complete pre-code age, immediate post-code age and real code original e(r), or it would weaken an already-verified result.
12. The proof of chronological pre≤post does not rely on the code source index r=c; all target coordinates use c=e(r).
13. The lex predicate is on genuine HensonOneType finite target old-neighbour words and uses 0<1, consistent with all-zero-first diary ordering.
14. A front of zero or one survivors has vacuous lex-sortedness. No Fin(0) witness is used in the proof.
15. The lex corollary does NOT prove the order of two daughters created at a later split, whose first difference can arise at the new pivot; split daughter naming remains a separate geometric obligation.
16. It also does not prove full dependent Kpt L+/E/B3 word identities, actual selected meet/split chronology, 24-case enumeration, or exact BRD lower bound.
17. No frozen black manuscript text should be changed. The corresponding TODO may be updated after the exact-head kernel compilation and strict standard-only axiom gates pass.

## Lean acceptance

1. On a new branch, minimally strengthen the public theorem k4_full_actual_zero_code_ordinary_age_step by adding the genuine pre→post chronological extension and exact neighbour set identity conjunct.
2. Derive it directly from the *existing hPreRealSurvivors* and the local post_i := restrictPrefix(t_i,c+1), without assuming extra geometry or editing other verified proofs.
3. Prove a separate standalone corollary target lex-sortedness for the full pre-code target family, real immediate post-code survivors and later synchronized target survivors under the one input invariant IsTargetLexSorted old.
4. Test original full theorem, stronger new public statement and lex corollary with exact-head Lake build and strict named standard-only transitive axiom report, alongside whole repository Lean CI. The global diary lower bound remains explicitly UNVERIFIED.
