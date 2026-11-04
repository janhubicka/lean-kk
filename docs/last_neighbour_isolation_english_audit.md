# English-first theorem and adversarial audit: isolated last-neighbourhood witness

**Date:** 4 November 2026. **Status:** English proof and hostile mathematical audit; commit this note **before** introducing the Lean formalization.

## 1. The mathematical theorem

Let `E : Nat -> Nat -> Bool` be an original-edge table, let `b,N,q` be natural numbers with `q>0`, and let `U` be a finite set of previously reserved original indices. Assume a proposed adjacency column `c_old` has **no directed q-clique among its old neighbours below b**.

Assume that for every `y in U` there is some finite `S_y` (which may depend on `y`) such that

* `y in S_y`;
* `|S_y| < q`;
* for every `x < y` with `x notin S_y`, the ACTUAL original graph has `E(x,y)=false`.

Set the new column on `[0,N)` by
`c(x) := if x < b then c_old(x) else decide (x in U)`.
Then **the complete old neighbourhood of c below N contains no directed q-clique**. This includes every older selected vertex, split/coding parameter, gap vertex, and reserved original; no false blockwise projection or arbitrary future-vertex restriction is used.

## 2. English proof before formalizing

Assume a directed q-clique `C` of neighbours below `N`. Because `q>0`, choose its **largest actual original index** `y`. If `y<b`, every vertex of `C` lies below `b`. The prescribed old column agrees with `c_old` there, so `C` contradicts the negative old-neighbourhood certificate.

If `y>=b`, the fact that `y` is a neighbour says `y in U`. Choose `S_y` as above. Every `x in C - {y}` has `x<y`; the complete directed-clique condition gives `E(x,y)=true`. By contraposition of the last-isolation assumption, `x in S_y`. The largest vertex `y` itself is in `S_y`, hence `C ⊆ S_y`, contradicting `q=|C| > |S_y|`. This completes the proof.

**Key strengthening:** explicit cross-block nonedges or even a partition of U are unnecessary for this restricted *freshly isolated* situation. Every forbidden mixed clique would be trapped inside the small isolation block of its maximal vertex.

## 3. Geometric specialization to the genuine Henson enumeration

Assume the normalized Henson avoidance condition, and separately the **exact complete-column** `OnePointLeftDense E ell` property stipulated for the chosen enumeration.

For a finite list of sizes `r_i<ell-1`, invoke the already Lean-verified `henson_leftDense_ordered_reserved_blocks` to choose genuine isolated reserved cliques `S_i`, all beyond a starting prefix `b`. Let `U` be their finite union, and put `N=max(b, sup U + 1)`. Since the actual chosen blocks satisfy the old-outsider isolation condition, the preceding theorem applies with `q=ell-1` whenever the prescribed old selected-prefix column is certified negative. Thus the complete neighbour certificate for the next selected original is negative. `henson_leftDense_realizes_certified_original` gives a **genuine later original** `v>=N` with all prescribed passing bits before `N` and zeros for **every intervening old index** in `[N,v)`, in both directed orientations.

This is a real one-step selected extension after an arbitrary finite fresh family of blocks. It does **not** assert that an entire recursively specified macrodiary uses only fresh isolated blocks, or that future selected vertices see no old reserved blocks.

## 4. Adversarial objections and precise repairs

1. **The maximum needs q>0.** Without it, an empty q-clique would defeat any nonempty-neighbourhood argument. In the Henson application `q=ell-1`, and `ell>=2` suffices.
2. **Use the actual old graph E, not only a graph-age shadow.** The proof compares `E(x,y)` for the real original indices of the chosen block. No inference from selected-age equality to corrected B3 is permitted.
3. **No claimed isolation toward later outsiders.** The proof uses `x<y` and selects the *greatest y*. It never incorrectly infers that the earliest reserved original is nonadjacent to later gap vertices.
4. **The requested column is zero on post-b outsiders.** If older selected originals or coding parameters beyond b are prescribed as positive neighbours while linked to old blocks, the conclusion can fail. Such later stages still require the exact interaction-pool certificates from PR #50.
5. **Strict size bound is necessary.** If an entire `(ell-1)`-clique is included in the selected column, its extension is forbidden; PR #51 formalizes this counter-boundary.
6. **All gaps are included.** The new original appears after `N`, potentially skipping enumeration indices. The complete-column left-density property forces zeros at every skipped index and both orientations.
7. **No division into blocks is assumed in the generic theorem.** A choice of one suitable `S_y` for each positive reserved neighbour suffices. This avoids a hidden uniqueness or disjointness hypothesis (empty blocks are harmless).
8. **No infinite existence or optimality claim.** Finite one-point safety and genuine realization do not establish the unbounded resolved-copy schedule, numerical-H dependent E/auxiliary I1-I3/B3 closure, or a common labelled inverse source orbit. The unconditional big Ramsey upper and lower bounds remain open.
9. **No circular appeal to desired safety.** The old negative certificate is explicit, and the new one is a theorem conclusion; the combined corollary must build U and verify all last-isolation hypotheses from PR #51, not assume the sought new certificate.

## 5. Lean deliverables / test gate

* In `Kk/LastNeighbourIsolation.lean`, prove `finiteNeighbourCliqueCheck_false_of_last_isolated` by picking `Finset.max'` from a purported clique and then splitting at `b`.
* Define a finite union of the actual reserved block list, prove its element specification, and derive a genuine selected-successor existence theorem from PR #51 and `henson_leftDense_realizes_certified_original`.
* Include the two new theorem endpoints in `scripts/check_axioms.lean`, add the module to `Kk.lean` and retain only `propext`, `Classical.choice`, `Quot.sound`.
* Edit only the olive/green successor-proof explanation in `kk.tex`, and add exact validation markers **only after successful full Lean CI**. Protected black text gets TODO notes, not direct rewrites.

**Verification status:** at the moment this English note was committed, the new Lean source did not yet exist and no new Lean validation was claimed.
