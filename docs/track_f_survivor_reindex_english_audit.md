# Track F — deleting a coded coordinate: exact finite survivor reindexing

**English proof and adversarial audit, 14 November 2026, before Lean.** This continues the fully merged literal word-column module and the general same-index monotone-raw locality theorem, but solves an additional issue: deleting a coded branch changes the sorted carrier from `Fin (d+1)` to `Fin d`. An isomorphism of raw age formulas across two dimension types is a real theorem; no implicit coercion of coordinate sets is permitted.

## Definition and statement

Let `ell>0`; fix natural numbers `d,e` and an injective map `f : Fin e ↪ Fin d` selecting and ordering the surviving branches. For each admissible nonempty support `U : IntegerGraphSupport e ell` define the full support `f_*(U)` by its image under f. The image is nonempty and has cardinality ≤ |U| ≤ ell-1.

For any raw bound `B : IntegerGraphSupport d ell → Nat` define the **reindexed raw bound**
`f^*B(U) := B(f_*(U))`.

Assume **raw support monotonicity** of B: for all admissible `S⊆T` in the full d-dimensional support set, `B(S)≤B(T)`. The claimed exact theorem is

`G_(f^*B)(U) = G_B(f_*(U))` for every admissible `U : IntegerGraphSupport e ell`,

where G is the *actual* finite integer-clique-weight supremum canonicalizer, not an invented replacement. In particular `ell>=2` suffices, but `ell>0` is the convenient Lean hypothesis to form the zero weight in `Fin ell`.

This handles **arbitrary noncanonical raw bounds B**, provided they are monotone. It immediately applies to the word raw bounds `trackFWordRaw d ell cols`, whose monotonicity was proved in merged Track F PR #130.

For the actual deletion of coded j from d+1 branches, take the canonical order-preserving embedding `Fin d ↪ Fin (d+1)` that skips j (e.g. `Fin.succAbove j`). The finite chronological columns on remaining branches are `cols.map (fun c i => c (f i))`. The *literal common-letter predicate* is preserved along f, so the reindexed raw bound is exactly the pullback `f^*(trackFWordRaw original cols)`. The canonical-age theorem yields the desired deletion bridge.

## Proof of the canonicalization identity

Fix a support U on the e-dimensional survivor sort.

**Direction (G_B(f_*U)\le G_{f^*B}(U)):** Let w be any normalized B-feasible d-vector with total weight ≤ell-1. Restrict to the selected coordinates by setting `v(i)=w(f(i))`. Because f is injective, the sum of the v-coordinates is the sum of w over the image of f, at most its full total. For each survivor support S, the S-total of v equals the f_*(S)-total of w, so it is bounded by B(f_*(S))=f^*B(S). Hence v is a normalized f^*B-feasible vector and retains the exact U-total of w. Supremizing gives the inequality.

**Direction (G_{f^*B}(U)\le G_B(f_*U)):** Let v be any normalized f^*B-feasible e-vector. Extend it to the full d coordinates by assigning v(i) at f(i), and zero outside the image of f. Its total size is exactly that of v and so ≤ell-1. To check a full admissible support V, set Q=V∩im(f). If Q is empty, the V-total of the extended vector is zero. Otherwise Q=f_*(S) for the unique nonempty survivor support S=f^{-1}(Q); because f is injective, |S|=|Q|≤|V|≤ell-1. Feasibility on S gives mass(Q)≤f^*B(S)=B(Q), and **raw monotonicity** gives B(Q)≤B(V). Thus the zero extension is feasible for every full V. Its f_*(U)-total equals v(U), proving the reverse inequality by supremizing.

This is exactly the missing finite **dimension-change** result. The existing same-index locality theorem is related but cannot replace the construction of the two witness transfers.

## Separate literal-word raw bound lemma

For any nonempty survivor support U, its image f_*(U) consists precisely of the original active words now represented by U. In each chronological column c, a positive letter n is common to every survivor branch i∈U **iff** it was common to every original branch f(i)∈f_*(U). Therefore the largest common positive symbol, and hence `ell-1-max n`, is identical before and after deleting the omitted coordinates. This identity is independent of age canonicalization and is valid even when the old raw function has slack.

**Quantifier and edge guards:** The lemma is independent of the word-based E edge predicate and does not assert that j is a controlled coding pair. It applies to any injectively selected subset of active words. A deletion identity by itself does not prove the subsequent one-column passing-bit relation or the full diary inverse.

## Adversarial checks

- **Monotonicity genuinely necessary:** K4, d=2, B({0})=B({1})=3 but B({0,1})=1. The full canonical single-sort value at {0} is 1, while after deleting coordinate 1 the new one-sort raw bound 3 canonicalizes to 3.
- **Injectivity necessary:** A non-injective f collapses distinct survivor weights; their summed mass cannot be identified with the weight of one full sort. A mere function f is not an acceptable substitution for an embedding.
- **Empty intersection:** Q=∅ is not an `IntegerGraphSupport` and must be handled separately, with zero mass.
- **Finite normalization:** The total-weight cap ≤ell-1 and each coordinate in `Fin ell` are part of the established actual K_ell graph-age definition, not an extra hypothesis.
- **Raw slack allowed:** The result is not restricted to already canonical F; imposing `B=G_B` would make it weaker than the manuscript's concrete-word claim.
- **Order matters for diaries, not capacities:** Although the numerical age formula is invariant under reordering columns, the chronological age decorations must still be retained for the eventual full diary inverse.
- **Survivor order matters for labelled codes:** f is an *ordered* embedding for actual deletion. An arbitrary injection proves the raw capacity theorem but preserving lexicographic branch labels and terminal adjacency is a separate concrete-diary step.
- **No BRD conclusion:** Nothing here proves non-free splitting, E/X under the positive-spectrum invariant, the full abstract–concrete diary bijection, or any independent infinite unavoidability theorem.

## Formalization gate

New file `Kk/TrackFSurvivorReindex.lean`, with targeted declarations:
1. `trackFMapSupport`: image of admissible nonempty support along an embedding;
2. `trackFRestrictColumns` and `trackFWordRaw_restrict_columns`: exact literal-word raw reindexing;
3. `trackFRestrictWeights` and `trackFExtendWeights`: actual normalized clique witness maps;
4. `trackFCanonical_reindex_mono`: canonical age commutes with survivor injection, under raw monotonicity;
5. `trackFWordCanonical_reindex`: specialization to concrete word levels.

Run exact-head targeted module build, strict standard-only `#print axioms` checks, and ordinary full repository build. No `sorry`/new axioms and no mutations of central `Kk.lean` or the protected manuscript proof. Keep the full diary lemma pending.
