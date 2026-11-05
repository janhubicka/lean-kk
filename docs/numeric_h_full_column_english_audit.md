# English-first bridge: complete original-to-top binary column in actual numerical H

**5 November 2026. Proof before code.** This note is committed *before* the Lean source, followed by an independent hostile audit. Scope: literal binary L-atoms of the actual numerical H constructor; this is not the auxiliary E relation, the Algorithm 5.4 parameter-closed B3 continuation, or a common labelled inverse source.

## A. Exact top gate on EVERY earlier original generation

The actual numerical-H binary constructor on real positions is controlled by the **verified exact generation gate**:

For original i<j, generations q,m≤k, and directed relation bit B(i,j,r),

  H.binary(ι(i,q),ι(j,m),r)=true
  iff (q<m OR (q=m AND m=k)) AND B(i,j,r)=true.

Set m=k. For **every q≤k**, the generation condition is automatically satisfied: either q<k or q=k=m. Therefore, for all i<j and every q≤k,

  H.binary(ι(i,q),ι(j,k),r)=B(i,j,r).

This is an EXACT Boolean equality, not merely a positive-edge lemma. It propagates both positive and absent older-original-to-new-top bits, even when the older original is also copied at top generation q=k. It is a direct theorem over the genuine `infiniteNumericHL` definition, with no change to the base graph.

For symmetric Henson E, its normalized binary B is symmetric; the verified `hNumericBinary_symmetric_of_base` theorem ensures the reverse directed tuple has the same value. Hence

  H.binary(ι(j,k),ι(i,q),0)=E(j,i)=E(i,j)

for every q≤k. Neither direction should be assumed merely from undirected informal notation.

## B. Nonedges across EVERY old-to-new reserved generation pair

Suppose i<j and actual original graph E satisfies E(i,j)=E(j,i)=false. The numerical-H generation gate can only DELETE old positive atoms; it cannot create a positive atom absent in E. Therefore the already-verified `numericH_preserves_original_nonedge`, plus actual symmetry, gives for ALL q,m≤k:

  H.binary(ι(i,q),ι(j,m),0) =
  H.binary(ι(j,m),ι(i,q),0) = false.

Unlike the designated-generation positive pair theorem, this is ALL generations, including top and non-designated auxiliary generation copies.

## C. The genuine fresh-block / old-linked selected successor

Use the verified conditional geometric theorem `henson_leftDense_later_selected_after_fresh_blocks_of_link_capacity` from PR #56. Its hypotheses explicitly include:
* normalized genuine Henson forbidden-family avoidance;
* independently stipulated complete-column `OnePointLeftDense E ell`;
* an actual old original-index cut `base`, arbitrary older reserved-block tagging and complete proposed old column `oldNeighbour`;
* genuine old cross-block nonedges, a negative complete pure-unreserved old-neighbour checker, and strict actual old-block link-capacity budgets;
* any FINITE list `sizes` of fresh reserved clique sizes `r<ell-1`.

That theorem returns actual fresh original-index cliques `fresh`, an original cut `front` above all of them, and a genuine selected original `v≥front` in the SAME UNMODIFIED graph E. All fresh originals are ≥base and <front; all old-to-fresh original atoms are zero both ways; all fresh blocks are internally cliques and pairwise cross-free. The selected original `v` has its complete old column, with ALL skipped indices:
  E(x,v)=E(v,x)=
    oldNeighbour(x), if x<base;
    1, if base≤x<front and x belongs to a fresh block;
    0, otherwise for x<v.

Combine with A for k=ell. For every actual older original x<v, and EVERY real-generation q≤ell, the actual H binary L atom from its generation-q copy to the selected top-generation copy (and reverse) equals EXACTLY that prescribed bit. This covers all previous selected originals, all old reserved auxiliaries, split/coding parameters, unused old originals, newly reserved originals and any intervening original indices.

Combine with B. For every old original x<base and each fresh reserved original y, and for EVERY q,m≤ell, the numerical-H copies are mutually nonadjacent in both tuple directions. This is a TRUE all-generation old-to-fresh invariant, not merely a marked-gadget statement.

Because the fresh blocks are genuine original directed cliques, the already-verified `numericH_designated_clique_of_finite_set` simultaneously supplies their positive designated-generation numerical-H clique edges. These three conclusions together give a meaningful literal numerical-H **L-reduct** realization of the prescribed finite selected-plus-fresh-block step.

## D. Hostile adversarial audit

1. **Do not confuse L with auxiliary E.** The exact binary real-generation gate is an L-atom theorem. It does NOT prove any auxiliary E record or the full dependent corrected-B3 test.
2. **The older top generation q=k must be included.** The gate explicitly permits q=m=k, not merely q<m. A proof restricted to lower-generation old auxiliaries would miss older selected top copies.
3. **Complete negative bits, not only positives.** Use Boolean equalities, so all old parameter and skipped-gap zero passing bits are verified; do not merely cite positive designated clique copying.
4. **Both tuple orientations.** The general directed forward theorem does not make the base symmetric. In the Henson specialization symmetry is derived from actual avoidance of BOTH asymmetric forbidden ordered patterns; use a checked numerical-H symmetry lemma or an exact reverse direction proof.
5. **Chronological original indices matter.** The gate theorem assumes i<j; for selected v the genuine original left-density conclusion guarantees x<v for every previous original x. Do not reason from numerical address ordering alone.
6. **No arbitrary edge edits.** The old graph E, old reserved blocks, all older selected originals and actual numerical H coordinates are fixed. The proof chooses genuinely later Henson original indices and uses the literal H constructor.
7. **Fresh block size sharpness.** For a new selected vertex joined to its whole fresh reserved clique, each block has r<ell-1. A block of size ell-1 joined to the selected vertex would violate K_ell-freeness. This is already a checked regression in PR #51.
8. **Old selected column safety is NOT automatic.** The combined theorem retains the actual negative pure-unreserved checker and live old-block capacity budgets. The theorem does not prove the proposed unbounded macrodiary generates only such legal old columns.
9. **Every generation is relevant.** Old-to-new reserved absent edges must be certified for arbitrary q,m≤ell, not just their designated increasing generation copies; the old-to-new original nonedge proof and all-generation H nonedge lemma cover that.
10. **Freshness across gap original indices.** The actual Henson left-density theorem supplies zero selected passing bits at ALL intermediate enumeration indices between front and v; no blanket statement is made about unrelated edges involving those gaps. The numerical H copy preserves exactly those specified selected-to-gap bits.
11. **Positive selected-to-fresh atoms are consequences, not extra assumptions.** Every fresh y lies in the union of fresh blocks, so E(y,v)=true by the actual selected column. The full top gate makes its H atom true for every generation q≤ell, not just the designated q=a.
12. **The cover-age algebra is separate.** PR #65 proved that genuine integer-witness graph-age covers restrict to covers/equality on any selected subfront. Present theorem proves some actual numerical-H L atoms; it does NOT identify their graph-age function with a requested canonical cover drop or prove that the numerical-H gadget creates no extra selected-front constraints.
13. **Full B3 and inverse orbit still open.** The verified numerical-H K4 cut-10/cut-22 counterexample includes an extra auxiliary interesting level. Exact old-to-new L-atom copying alone does not rule out such extra (I3) microevents, classify their source nodes or force two occurrences to share a labelled inverse-source orbit.
14. **This is finite one-step geometry, not an induction.** No claim that the next selected event automatically passes old-block budgets or maintains full assigned source types.

## E. Formalization contract

Create `Kk/NumericHFullSelectedColumn.lean`. First kernel-prove the generic exact all-old-generations-to-top forward bit equality from `hNumericBinary_real_forward_iff`; then exact Henson symmetric two-directed equality. Prove all-generation both-directed preservation of actual old-to-fresh nonedges. Finally combine *actual original* PR #56 construction with exact all-old-to-top H columns and all-generation old-to-fresh zero bits in one named genuine selected-plus-fresh-step theorem. If feasible, carry designated-generation positive clique records explicitly; do not add hypotheses beyond the previous source theorem.

Register source-exact new Lean endpoints with the strict transitive-axiom whitelist, verify full CI, and only then add green markers to the OLIVE manuscript successor proof. Never edit protected BLACK prose; leave clear TODO notes for canonical-cover age-realization, B3 and orbit.
