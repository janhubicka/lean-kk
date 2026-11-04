# English-first proof and adversarial audit: exact four-quadrant live-pool update

**4 November 2026 — write and audit the mathematics before implementing Lean.**
This note was committed BEFORE the Lean code. It concerns actual finite original-edge tables, NOT the full parameter-closed corrected B3 continuation relation.

## 1. Exact live-set and linked-set update

Let `E : Nat → Nat → Bool` be an arbitrary directed Boolean original-edge table. For finite sets `U,R` of original indices define

  `Link_E(U,R) = {x ∈ U : ∃ y ∈ R, E(x,y)=true}`.

Here `U` is the set of unreserved positive neighbours of the proposed selected original, and `R` is the set of live reserved positive neighbours of **one specific reserved block**.

For a previous and next proposed selected column let the finite sets be `U0,R0` and `U1,R1`. Define:

- `UK = U0∩U1` (unreserved candidates kept), `UA=U1\U0` (new positive unreserved candidates, possibly enumeration gaps);
- `RK = R0∩R1` (reserved witnesses still live), `RA=R1\R0` (newly live reserved witnesses).

The EXACT formula is

`Link_E(U1,R1) = Link_E(UK,RK) ∪ Link_E(UK,RA) ∪ Link_E(UA,RK) ∪ Link_E(UA,RA)`.

This is true without assuming `U0⊆U1`, `R0⊆R1`, symmetry, loop-freeness, K-ell-freeness, Henson density, or any chronological ordering. It is intentionally more general than the one-vertex insertion recurrence in PR #58.

### English proof

Since `U1=(U0∩U1)∪(U1\U0)=UK∪UA` and similarly `R1=RK∪RA`, a linked vertex `x` is exactly a member of `UK∪UA` for which some `y∈RK∪RA` satisfies the **actual directed edge** `E(x,y)=true`. The four exhaustive membership alternatives give the displayed union. Each alternative is a genuine link to a live next-stage reserved vertex, giving the converse inclusion. No leftover links via deactivated reserved witnesses are incorrectly retained.

The formula handles *deletions* as well as additions. In particular, `Link_E(U0,R0)` itself is NOT generally a subset of `Link_E(U1,R1)`, and it is mathematically wrong to update the new pool by simply adding newly linked vertices to the entire old pool.

### Changed tag spaces and actual Henson columns

Use PR #49's exact existing definitions for an original prefix, a reserved-block tagging function, and a proposed passing column:

- `liveUnreserved N B block neighbour`;
- `liveReservedBlock N B block neighbour b`;
- `linkedUnreserved E N B block neighbour b`.

A next selected macrodiary event may have a different prefix length **and a different number of reserved block identifiers** `B0` and `B1`. To compare a next block `b:Fin B1` with an older one, provide an explicit optional matching `previousLabel : Fin B1 -> Option (Fin B0)`. If unmatched, its old live reserved set is empty. If matched, use the actual previous live reserved set. In every case the four-quadrant formula gives the EXACT new `linkedUnreserved` from the actual old/new tag functions, passing columns and prefix lengths. The identity remains valid for *any* matching, but one must prove that a chosen matching has the intended geometric meaning before using it to claim a canonical diary invariant.

### Complete mixed-neighbourhood certificate

With genuine cross-block nonedges for the NEXT tagged blocks, the exact PR #50 reduction and PR #54 sufficient clique-capacity theorem apply. For every new block b, compute `R1_b` and the exact updated linked set `Link_E(U1,R1_b)` using the four quadrants. If

- the complete **pure-unreserved** next q-clique checker is negative, and
- `|R1_b|+cap_E(updatedLinked_b)<q` holds for all new block b,

then the entire next selected old-neighbourhood checker is negative. Under the separately stated normalized Henson age avoidance and complete-column one-point left density, the next selected original is genuinely realized, with exactly its prescribed passing column and all intervening gap bits zero in both orientations.

This is an executable bookkeeping and certificate interface, NOT a proof that the manuscript's deterministic macrodiary actually satisfies the tests.

## 2. Adversarial objections and regression targets

1. **Deactivated reserved witness cannot be reused.** Example: old live block `R0={0}`, new live block `R1={1}`, and unchanged unreserved `U0=U1={2}`; set `E(2,0)=1`, `E(2,1)=0`. Old linked pool is `{2}`, new linked pool is empty. Updating by `oldLinked ∪ newLinks` is FALSE. The quadrant formula discards stale links correctly.
2. **An unreserved positive neighbour can itself deactivate.** Example: `U0={2}`, `U1=∅`, unchanged live R; new linked set is empty even if `E(2,R)=1`. The formula uses `U0∩U1`, not the entire old U.
3. **Newly positive gaps matter.** If `x` was not an old positive unreserved neighbour but appears in the new range/passing column, it lies in `UA` and its edges to both retained and newly active reserved witnesses are tested. No silent gap deletion.
4. **Changing reserved block labels is not an isomorphism.** The optional old-label correspondence is just an explicit comparison input; the exact formula does not imply that the intended canonical parameter assignments line up. This still needs source-node-wise envelope comparison.
5. **The linked predicate is directed.** PR #49 defines `E(x,y)=true` from unreserved `x` to reserved `y`. It is NOT the mutual adjacency predicate used when adding a vertex to a *directed clique* in PR #58. For genuine Henson undirected graphs both coincide by symmetry, but this generic finite update must retain the correct original orientation.
6. **Zero or empty blocks.** If no live reserved vertices remain, the linked set is empty. Unmatched new blocks have `R0=∅`; empty old tag space `Fin 0` should cause no fabricated old block.
7. **No complexity miracle.** The formula may have up to four finite terms, some with many edges. It is an exact change record, not evidence that the capacity budget always holds, nor a polynomial bound independent of `N`.
8. **The budget is sufficient, not necessary.** The previous counterexample of a safe mixed K4 pool with an overlarge sum `|R|+cap(L)` remains valid. Do not label a negative budget as a failed actual extension.
9. **No use of PR #58 insertion recurrence without a fixed subset.** PR #58's exact one-vertex update only applies to genuinely fresh inserted indices of a fixed linked set. The four-way formula handles switches first; any subsequent one-vertex optimization requires a verified exact enumeration of the newly linked part.
10. **No B3 projection.** The genuine numerical-H K4 first-auxiliary-cut obstruction refutes selected-age to full corrected B3 preservation. The present lemma is only about actual original graph edges and exact finite selected-neighbourhood tests; it cannot imply equality of complete upper L+ successor types or a common labelled monoid source.
11. **No global resolved-copy theorem yet.** The currently intended schedule must instantiate the actual old/new tagging and passing columns and prove the next pure-unreserved certificate, each budget (or exact pool test), and compatibility of dependent auxiliary E data. None of those geometric assertions is inserted as a hidden assumption of an unconditional theorem.

## 3. Formalization and independent checks

- Define `linkedOriginalsTo E U R` by a finite filter and prove distributivity under unions in both arguments.
- Prove the complete four-quadrant equality for arbitrary `U0,U1,R0,R1`, not just monotone updates.
- Define a finite explicit update object using arbitrary old/new `U,R` pairs, and specialize it to PR #49's real original prefixes / block tags / passing columns with optional old labels.
- Prove the complete next old-neighbourhood sufficient certificate via PR #54 and the quadrant equality. Provide the conditional real Henson selected-original realization.
- Include executable directed regressions for loss of a reserved witness and a newly activated link, and exhaustive independent small-graph testing in a separate manuscript referee.
- Add named transitive-axiom checks and require full `lake build` and strict whitelisted axiom audit.
- Edit only olive/green successor-manuscript prose; leave black text unchanged with TODO notes. Add exact green validation markers ONLY after successful CI.

