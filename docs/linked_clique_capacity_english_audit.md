# English-first theorem and adversarial audit: linked-unreserved clique capacity

**Date:** 4 November 2026. **Sequence:** This English proof and hostile audit are committed *before* the Lean source. No theorem is advertised as Lean-validated until complete CI succeeds.

## The mathematical reduction

Fix a finite original-index prefix `[0,N)` of a symmetric irreflexive `K_ell`-free graph (the finite combinatorial part below does not require symmetry). Let `q=ell-1>0`, and consider a proposed later selected original with Boolean old passing column `neighbour : Nat -> Bool`.

For every reserved-block identifier `b`, form the **genuine actual graph** subsets

* `R_b`: old vertices tagged as reserved in block `b` which are positive neighbours of the proposed selected vertex;
* `L_b`: *unreserved* old positive neighbours (including previously selected originals and split/coding parameters) joined in the actual original graph to **at least one** live vertex of `R_b`;
* `P_b=R_b union L_b`, its complete live mixed interaction pool.

Assume the actual old edge table has zero cross-edges between vertices of distinct reserved blocks. PR #50 then proves an exact decomposition: the COMPLETE neighbourhood is `q`-clique-free iff its pure-unreserved part is `q`-clique-free and every `P_b` is `q`-clique-free.

Define `cap_E(L)` as the greatest cardinality of a directed clique contained in the finite set `L`, with empty set capacity zero (it is computed by enumerating the finite powerset and taking the maximum). A useful *sufficient* per-block condition is

`|R_b| + cap_E(L_b) < q`.

Under that condition **every** directed clique in `P_b` has fewer than `q` vertices. Thus the negative pure-unreserved test, the genuine cross-block nonedge hypothesis and the `cap`-budgets imply the negative COMPLETE neighbourhood checker. Under normalized Henson avoidance and the separately assumed complete-column left-density condition, the next selected original is genuinely realized in the *unchanged* Henson enumeration, with exact prescribed passing bits and no intervening positive edges.

## English proof, step by step

### Finite capacity bound

For any finite sets `R,L` and any directed clique `C ⊆ R union L`, let `C_R = C intersect R` and `C_L = C intersect L`. We have

`|C| <= |C_R|+|C_L| <= |R|+cap_E(L)`.

Indeed, the first inequality is simply the cardinality-of-union inequality, the second uses `C_R ⊆ R`, and `C_L` is itself a directed clique contained in `L`. Hence if `|R|+cap_E(L)<q` there is no directed `q`-clique in `R union L`. This proof does **not** need `R` and `L` to be disjoint, although the actual graph tagging makes them disjoint.

### Later selected vertex

For every block `b`, apply the preceding lemma with `R_b,L_b`; by definition their union is precisely the **actual** mixed pool `P_b`, with all older unreserved links retained. Every `P_b` has a negative size-`q` clique checker. Combine these with the negative pure-unreserved size-`q` checker through the already kernel-checked `finiteNeighbourCliqueCheck_false_iff_exact_mixing_pools`. This produces a negative checker for the entire proposed selected old-neighbourhood. With `q=ell-1`, the existing `henson_leftDense_realizes_certified_original` theorem produces a later real selected original with exactly that old adjacency column and zero passing bits on every skipped index in both orientations.

The construction is **conditional on explicit local numerical tests**, rather than a proof that a predetermined macrodiary always passes them. Unlike the fresh-block maximum-index theorem in PR #52, it allows earlier selected originals occurring *after* old reserved vertices and genuinely adjacent to them.

## Hostile audit: attempts to invalidate the lemma

1. **Do not substitute vertex cardinality for clique capacity.** Prior PR #49 used `|P_b|<q`, unnecessarily restrictive when older linked selected vertices are numerous but mutually nonadjacent. This criterion remains valid if `L_b` has many elements and small clique number.
2. **No claim of necessity.** A block may satisfy `P_b` being `q`-clique-free even though `|R_b|+cap_E(L_b)>=q`: some `R_b` and `L_b` clique witnesses may be incompatible across the boundary. The capacity budget is a sufficient strengthening, not an equivalence.
3. **Cross-block edges cannot be silently discarded.** PR #50 requires genuine zero original edges between **different** tagged reserved blocks. PR #51 constructs this for finite families of fresh reserved cliques under complete-column left density, but a global diary with arbitrary reserved steps still needs its own exact cross-block preservation proof.
4. **Keep older unreserved parameters, not just labelled selected vertices.** `L_b` includes every old nonreserved neighbour linked to a live reserved vertex, whether it is selected, an auxiliary parameter or a gap original. Ignoring any of these can make a false negative certificate.
5. **Use the actual old-original graph, not B3 future-type relations.** `cap_E(L_b)` is computed from the original old edge table, and PR #50 applies to old cliques. It does **not** compare allowed future-to-future edges in the full parameter-closed corrected B3 test. The real numerical-H K4 cut-10/cut-22 obstruction remains.
6. **Zero threshold and empty blocks.** In the final Henson application `q=ell-1>0`. An empty `L_b` has capacity zero. A block of size `q` with all vertices live fails the strict budget, as required by PR #51's obstruction.
7. **No limit on the *number* of linked old selected vertices.** Example for `K_4`: one reserved original `0`, two later selected originals `1,2` adjacent to `0` but not each other, and the proposed new selected vertex adjacent to all three. Then `|R|=1`, `|L|=2`, but `cap_E(L)=1`, so `1+1<3` certifies safety. The old neighbourhood is a star, not a triangle. Adding the edge `1--2` raises capacity to two and creates the forbidden `K_4` upon the new selected vertex. This is a **genuine older-selected/old-reserved mixed-link case**, not a fresh-block-only case.
8. **No circularity from left density.** The Boolean negative certificate follows before invoking `OnePointLeftDense`. Left density is used solely to select a genuine later original realizing that already-certified column.
9. **Distinguish two versions of clique capacity.** The maximum is taken over **directed** cliques, with both orientations tested. The full Henson graph does satisfy symmetry via normalized age avoidance, but the abstract combinatorial lemma does not silently assume it.
10. **Still no global schedule or common orbit.** Proving that *the intended unbounded canonical macrodiary* satisfies these budgets (or the exact PR #50 tests) at each stage remains open. Full I1/I2/I3/B3 source-node assignments and the common labelled inverse source are independent remaining problems.

## Formalization and checking contract

* Define `finiteDirectedCliqueCapacity E P` by taking `Finset.sup Finset.card` over the directed cliques of the finite powerset of `P`.
* Prove `directedClique_card_le_capacity`.
* Prove `finitePoolCliqueCheck_false_of_reserved_plus_link_capacity` for generic finite `R,L` (no cross assumptions).
* Prove `finiteNeighbourCliqueCheck_false_of_link_capacity` and `henson_leftDense_realizes_later_selected_of_link_capacity`, using the actual `liveReservedBlock`, `linkedUnreserved` and PR #50 exact decomposition.
* Include a **real mixed-link K4 regression**, where `|L|=2` yet its clique capacity is one, plus a negative test after inserting the missing linked-selected edge.
* Register every public theorem endpoint in `scripts/check_axioms.lean`; keep the strict axiom whitelist.
* Edit only olive/green successor-prose explanation in `kk.tex`, and give exact green markers **only after CI has genuinely passed**. Black text stays unchanged.
