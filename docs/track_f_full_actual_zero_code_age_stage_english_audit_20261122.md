# Track F — fully physical ordinary-L zero-code age stage, from one invariant checkpoint

22 November 2026, evening. English proof and hostile audit BEFORE Lean.

This is the intended direct use of the real-survivor non-dummy age theorem drafted in Track F PR #488, and of fully verified source/target numeric age equalities (#482), actual rank-zero code selection (#424), source/target survivor resynchronization (#433), genuine target code-prefix front (#470), physical deletion/reindexing (#475), and exact zero-cut survivor age (#447).

## Initial genuine checkpoint

Fix normalized K4-free target E_t and a source E_s, with an arbitrary injective induced ORIGINAL-index graph map e (NOT assumed enumeration-preserving). Let OLD SOURCE one-types u_i and OLD TARGET one-types v_i, i∈Fin(d+1), be genuine, pairwise distinct, at common source level m_s and target level m_t respectively. For every i assume:

* genuine singleton ranks agree, rank(v_i)=rank(u_i);
* the ACTUAL source coding-node fibre of v_i is rank(u_i)-large above u_i;
* the COMPLETE physical canonical numerical integer graph-age of the old source tuple equals that of the old target tuple, in the SAME coordinate labelling. This is the true induction invariant of earlier synchronization (#410/#482), NOT an age equality automatically implied by rank matching.

Choose coded sort j with rank(u_j)=0 (manuscript singleton bound one). Prescribe an arbitrary finite set past of already selected SOURCE original indices, with all bits of u_j fixed before its source level zero at those past indices. This assumption cannot be omitted: a positive old edge cannot be erased. Choose target cutoff B beyond earlier selected target images and the old target prefix. Assume the genuine old TARGET canonical age F satisfies the legal zero-code equation on all admissible mixed supports T containing j: F(T)=F(T.erase j); singleton {j} is handled separately.

## Step 1: actual code original

Apply verified sourceCodingFibre_rank_zero_independent_code (#424) to (u_j,v_j), past, B. It returns an ACTUAL source coding one-type x, with source original index r=x.level and target image c=e(r), such that:

* u_j≤x and x belongs to the actual sourceCodingFibre of v_j;
* rank(x)=0, c>B, and r≥m_s;
* for every p∈past, p<r and the source and target ordinary edges in BOTH orientations between p,r and e(p),c are zero.

The target old-prefix membership of x gives m_t≤c without assuming order preservation of e.

## Step 2: real survivors and numeric age at the later checkpoint

Let f=Fin.succAboveEmb j be the exact order-preserving deletion of the coded TARGET sort. Put source survivor tuple u∘f and initial target survivor tuple v∘f. The injectivity, common levels, rank equality and actual large-fibre hypotheses of the original tuple restrict to these real survivors.

Apply verified k4_survivor_sync_after_zero_code (#433) at source original r and cutoff B. Obtain a common source later level M, a common TARGET later level H>c, genuine source later survivors w_i and target later survivors t_i, for i∈Fin(d), such that:
* all target t_i extend v_{f(i)}, are pairwise distinct, and have old target bit ZERO at c;
* the actual coding-node target fibres stay large above the respective source survivor continuations;
* the complete finite sorted K4 graph classes agree between original source survivors u∘f and later target survivors t.

Apply the verified full finite-class-to-numeric theorem (#478/#482) to obtain the equality of complete genuine canonical NUMERIC integer ages

  A_source(u∘f,m_s) = A_target(t,H).

Use the original FULL checkpoint numeric equality A_source(u)=A_target(v) and physical survivor canonical reindexing (#475) to deduce

  A_source(u∘f,m_s) = A_target(v∘f,m_t).

Therefore the actual OLD TARGET survivor age equals the actual LATER TARGET survivor age, on every admissible support including triples. This is not assumed as a new axiom and uses no raw=canonical shortcut.

## Step 3: construct the actual full target pre-code front at c

The constructor k4_construct_actual_precode_target_front (#470) uses a full later tuple indexed by Fin(d+1) with a placeholder at coded j, even though later survivors have only d entries. Build it explicitly with Mathlib Fin.insertNth:

  laterFull := j.insertNth dummy t,

where dummy is a genuine zero-pad of the original target code type v_j to common level H. It is NEVER selected as a future code branch; it is only an irrelevant placeholder to satisfy the older constructor's API. Since c<H and m_t≤c, dummy is valid at H. For each survivor index i, laterFull(f i)=t_i exactly by Fin.insertNth_apply_succAbove, and laterFull(j)=dummy.

The constructor's hypotheses for each surviving k≠j follow from Fin.exists_succAbove_eq, target extension v_{f(i)}≤t_i, and zero bits c∉N(t_i). For j, only the domain coverage c+1≤dummy.level is needed. This is not the dummy FAR type used in previous age-sandwich proofs: we never apply any age comparison involving laterFull at j.

Apply #470 using the ACTUAL coded node x. It produces a GENUINE full target pre-code type tuple pre indexed by Fin(d+1), all at exact level c, extending v_i on every coordinate, injective, with coded type pre_j equal to the genuine target original's old-column type at c (two-direction actual target edges, rank zero). Each survivor pre_{f(i)} extends into t_i. The entire pre-code age P is a genuine integer age below old F, and its coded singleton value is one.

## Step 4: derive WHOLE pre-code age equality without dummy

Apply the non-dummy real-survivor age theorem of PR #488 to:

  old = v, pre = the actual constructed pre, later = t,

with true chronological old≤pre and pre∘f≤t, numeric old/later survivor age equality from Step 2, coded singleton ranks zero and old legal zero-code law. The conclusion is the FULL equality

  CanonicalAge_target(pre,c) = CanonicalAge_target(v,m_t)

on EVERY admissible nonempty old support, including {j,i,k}; no intermediate profile equality and no fake continuation of the terminated coded branch was assumed.

## Step 5: immediate after-code age, reindexed exactly

For every surviving i, the constructor of pre gives
  N(pre_{f(i)}) = N(restrictPrefix(t_i,c+1)).
Verified zero-cut neighbour equality (#447) gives
  N(restrictPrefix(t_i,c+1)) = N(restrictPrefix(t_i,c)).
Thus the hypotheses of genuine physical survivor canonical deletion/reindexing (#475) hold. For EVERY admissible survivor support U:

  CanonicalAge_target(pre,c)(f[U])
      = CanonicalAge_target(restrictPrefix(t,c+1),c+1)(U).

Combining with the full pre-code equality from Step 4, the actual immediately-after-code survivor age equals precisely the old canonical age RESTRICTED to the genuine surviving target order. No phantom mixed support loss at c remains.

## Output and limits

One theorem can return genuine x,r,c, later t,H, and pre, with all required coding/past zero bits, common target levels, surviving target zeros and fibre largeness, plus the pre-code and immediate post-code complete canonical-age equalities. An actual source later survivor family w remains available as a witness for ongoing induction. Source e need not preserve chronological order. All full-support constraints and repeated sort multiplicities remain controlled.

This is the ORDINARY-L numerical/physical zero-code stage, NOT the full Kpt L+/E controlled-coding diary event. We have not proved every selected lexicographic split and meet, nor cover/split realization or BRD lower bound. The target-index tuple MUST be identified in the TRUE TARGET lexicographic order at the history checkpoint; the theorem only preserves the given Fin(d+1) coordinate labels and uses its exact successor-above deletion.

## Hostile audit

1. Initial FULL source–target canonical numeric age equality is a real induction invariant, not inferred merely from rank matching; verified #410/#482 provide suitable synchronized checkpoints.
2. The actual source code fibre must be rank-zero large and all already-fixed past bits zero; otherwise late nonadjacent code vertex need not exist.
3. Source selected original r may be arbitrarily out of order under e. All target cut comparisons use c=e(r), never r.
4. Target cutoff B must exceed past target images if the selected new image must come last; the theorem only guarantees c>B, not automatically B's relation to those images.
5. The original target v tuple must have a COMMON chronological level m_t and be injective; source u must also be common level and injective.
6. The original full checkpoint numeric equality requires identical sort labels. For a real diary the labels must already denote TRUE target lex-order branches; reindexing after each event remains an explicit additional task.
7. The normalized witness equivalence #478 is used only for canonical NUMERIC ages, not arbitrary RAW redundant support tables.
8. The survivor map Fin.succAboveEmb j is injective and order-preserving. It is never replaced by an arbitrary map that merges sorts.
9. In the target laterFull placeholder, only the coverage c+1≤level(dummy) is used. Do NOT treat dummy as an actual selected future code branch, nor apply age sandwich to it.
10. Fin.insertNth j dummy t must have exact identities at j and f(i); no guessed inverse index.
11. The pre-code type at j is built from the ACTUAL target original c and its genuine K3-free old-neighbour safety; it is not just a hypothetical target colour.
12. The full pre-code age P is genuine by #436 and bounded by old F by #438; its singleton age is one because true target rank is zero. These are kernel-checked, not postulated.
13. The old legal zero-code equation is needed on EVERY mixed admissible support, not only pairs. For singleton {j} the empty erasure is invalid, and exact rank one handles it separately.
14. Old/later survivor endpoint equality is DERIVED by two physical numeric equality statements and exact canonical survivor reindexing, not assumed independently.
15. The common later target level H must exceed c, and every true surviving target type must have zero bit at c in BOTH directed orientations. The source/target induced embedding and actual large fibre witnesses provide these zeros in #433.
16. Finite past may be empty; no source/target predecessor index is fabricated. If d=0 the survivor tuple is empty and the code step still has one actual coded branch.
17. Immediate post-code age equality is at EXACT levels c and c+1 and on the true survivor domain Fin(d); the empty support is not a graph-age coordinate.
18. The old source levels and target levels need NOT be equal. Source r≥m_s and target c≥m_t follow from actual coding-node refinement/fibre membership respectively.
19. Does NOT certify target lexicographic order or the precise meet/split event relation: these still require their own geometric argument.
20. Does NOT prove the complete diary lower bound, the 24 independent-triple enumeration, or the published diary characterization.
21. There must be no proof placeholder, sorry, new axiom, or explicit assumption of the desired pre-code equality. All connection lemmas must be stated with genuine actual Henson types.
22. The manuscript frozen black proof is unchanged; add a scoped note only after exact-head Lean and strict standard-only checks pass.

## Formalization strategy

Stack only after the no-dummy real-survivor age theorem (PR #488) passes CI. Reuse verified #424, #433, #470, #475, #478, #482 rather than rebuilding their mathematics. Start by proving a short Fin.insertNth target-survivor bridge with genuine prefix/zero data; then compose all five steps. Register strict named axiom checks and run full exact-head Lean CI. Do not promote global diary or BRD markers.
