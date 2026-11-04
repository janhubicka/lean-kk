# English-first proof and adversarial audit: one later selected stage with old links and new blocks

**Date:** 4 November 2026. This English proof and hostile audit are committed BEFORE the Lean file. They refine the finite old-link capacity result (PR #54) and the real fresh-block successor (PR #52).

## Statement in mathematics

Let `E` be the actual original-index adjacency table of a normalized `K_ell`-free enumerated Henson graph with the separately stipulated complete-column one-point left-density property, with `ell >= 2`.

Fix a finite *full original prefix cut* `base`. Mark its reserved original indices by `block : Nat -> Option (Fin B)`. Assume (a) original nonedges between **different** old reserved blocks, (b) the exact negative size-`ell-1` test on every unreserved older positive neighbour of a prescribed new selected column `oldNeighbour`, and (c) the sufficient live old-block **linked clique capacity budget** from PR #54 for every `b`: `|R_b| + cap_E(L_b) < ell-1`.

Given any FINITE ordered list of NEW reserved block sizes `sizes=[r_0,...,r_(m-1)]` with `r_i < ell-1`, there are actual new original cliques `S_i`, a cut `front` above all these indices, and a later actual selected original `v >= front` satisfying:

1. `S_i` has size `r_i`, all indices `>=base` and `<front`, induces a genuine directed clique in the original E, and every reserved `y in S_i` is nonadjacent in BOTH directions to each earlier `x<y` outside `S_i` (including gap originals).
2. Two different NEW blocks are chronologically ordered and completely nonadjacent in both directed orientations.
3. **New useful invariant:** Every original old-prefix `x<base`, selected, reserved, parameter or otherwise, is nonadjacent in BOTH directions to every newly reserved `y in S_i`.
4. The selected original `v` has exactly the prescribed `oldNeighbour` passing bits at every `x<base`, including positive edges to old reserved vertices when these were requested and legally certified; it has positive bits to precisely the union of newly reserved blocks between `base` and `front`; and it has zero bits to every other intervening index through `v`, in both orientations.

No changes are made to the graph `E` or the previously selected originals. This is an actual **one-step extension with old links plus fresh blocks**, not an assumed finite table or an arbitrary sequence of future stages.

## Proof, before Lean

By PR #54's `finiteNeighbourCliqueCheck_false_of_link_capacity`, the actual old-prefix column `oldNeighbour` has a NEGATIVE complete `(ell-1)`-neighbourhood checker, because the pure-unreserved old neighbours and every actual old mixed interaction pool pass the stated hypotheses. This is a mathematical conclusion obtained before choosing any new original.

Now invoke PR #52's `henson_leftDense_selected_after_fresh_block_family` with exactly this `oldNeighbour`, the genuine Henson forbidden-family avoidance, the assumed complete-column left density, `base`, and the fresh size list. It returns real new reserved clique blocks, a later selected original, their exact chronological order, mutual block nonedges, all earlier-outsider isolation, and the complete prescribed two-sided column (with gap zeros).

The only new point is (3). Fix `x<base` and `y in S_i`. The output gives `base <= y`, hence `x<y`. Also `x notin S_i`, because every member of `S_i` is at least `base`. Apply the earlier-outsider isolation property of `y` to obtain `E(x,y)=E(y,x)=false`.

Thus the new fresh blocks are not only cross-free among themselves but also cross-free to **all old original indices**, in particular every previously reserved block and selected/parameter vertex. The existing old-block cross-free invariant is preserved (the graph E was not modified), and the union of old and new reserved blocks remains cross-free.

## Hostile audit

* **Old links remain positive when requested.** Do not replace `oldNeighbour` by zero on all previously reserved vertices: that might destroy the canonical selected-front cover restriction. The current theorem allows old-reserved positive passing bits, but verifies their legality through the actual PR #54 budget.
* **Old block nonedges are still an explicit hypothesis.** This result does not conjure global cross-block nonedges from arbitrary selections; it can *preserve and extend* that invariant because each new block is fresh and isolated.
* **The old-prefix checker is complete, not selected-only.** It includes every actual older original, auxiliary split/coding parameter, and all positive old reserved links; no projection from graph-age data to corrected B3 is made.
* **Fresh sizes need the sharp bound.** Each new fully seen reserved clique has `r<ell-1`. A size-`ell-1` block would itself create an illegal new selected extension (verified in PR #51).
* **New actual gap vertices may have edges to older reserved originals.** This causes no false claim about the full old/new union: item (3) concerns ONLY the newly chosen reserved clique indices, not all later nonreserved gap indices.
* **The graph remains fixed.** PR #52 constructs real indices inside a fixed `E`, so no retroactive insertion or rewriting old original atoms is silently used.
* **Do not infer the NEXT stage's budget.** The newly selected original `v` may become a newly linked unreserved neighbour of the old reserved blocks, increasing `cap_E(L_b)` for a subsequent selected column. This theorem does not prove preservation of every budget without rechecking that next column.
* **No infinite recursion by a single quantified stage.** There is an interface suitable for induction, not a proof that a specified deterministic macrodiary supplies a negative pure-unreserved test and old-block budgets at ALL stages.
* **No B3 shortcut.** Ordinary original `E` edges and full corrected-(B3) upper-type tests are different. The genuine numerical-H K4 microcut obstruction still applies.
* **The condition is sufficient, not necessary.** Failure of the linked clique-capacity budget need not mean the exact PR #50 mixed-pool test fails: incompatible reserved/unreserved clique witnesses can prevent a forbidden clique even when their separate maxima sum to `ell-1` or more.

## Lean formalization contract

Use exactly `finiteNeighbourCliqueCheck_false_of_link_capacity` from PR #54 and `henson_leftDense_selected_after_fresh_block_family` from PR #52. State the full resulting existential geometry and strengthen it with **all old-original-to-new-reserved nonedges**.

Give no global assumptions hidden under a new predicate or theorem name; display `hCross`, `hPlain`, `hBudget`, and `hSmall` at the theorem boundary. Register the transitive axiom report in `scripts/check_axioms.lean`. Only add a green manuscript marker after actual complete Lean CI.

**Missing after this theorem:** actual per-stage verification of all old-link budgets for the prescribed unbounded macrodiary, full I1/I2/I3/B3 assigned upper types, common labelled inverse-source orbit and unconditional upper/lower big Ramsey degrees.
