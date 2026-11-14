# Track F — literal concrete-word column algebra (English first, 14 November 2026)

**Purpose.** Extend the separately Lean-verified age-cover and controlled-coding lemmas to the actual *chronological word columns* of the manuscript's Definition `Def:Concrete`. Those older theorems take a raw capacity function `B` as input; we must not assume without proof that appending a letter to concrete words imposes exactly the claimed raw cap.

**Ownership:** Independent Track F branch. The black manuscript prose and the global `Kk.lean`/central registry remain frozen for Track G integration. This audit is written before the Lean module.

## Literal finite column representation

Fix the number `d` of active branches, `ell`, and a common chronological length `m`. The letter in a column `c` at branch `i` is `c(i)` in `Nat`; a valid concrete diary eventually restricts it to `{0,...,ell-2}`. A finite ordered column history `C=[c_0,...,c_(m-1)]` is the transpose of `d` equal-length words.

For a nonempty admissible support `U` (i.e. `1<=|U|<=ell-1`), define `common(c,U)` to equal the unique positive symbol occurring **identically on every branch in U in column c**, or zero if the symbols are mixed or all zero. A convenient computation chooses the least member `r(U)` of U, compares every `c(i)` with `c(r(U))`, and returns that common value on equality, zero otherwise. Because U is nonempty, the result is independent of the chosen representative. The definition agrees with `c_n(U)` from the manuscript for every `n>0`.

The raw bound of the word history is

`phi_C(U) = min{ell-1, ell-1-common(c_0,U), ..., ell-1-common(c_(m-1),U)}`.

For letter values in `{0,...,ell-2}`, this is precisely `ell-1 - max{n : c_n(U)}` with `c_0(U)` always true, i.e. the manuscript's `phi_D`. The first formula also defines a harmless total natural-number function for arbitrary raw columns.

## Exact new-column lemma

Fix `T subseteq Fin d` and `n>0`. Define the *literal concrete append column*

`a_(T,n)(i) = n if i in T; 0 otherwise`.

For every nonempty U,

`common(a_(T,n), U) = n` if `U subseteq T`, and 0 otherwise.

**Proof.** If U⊆T, all entries indexed by U equal n. If U⊈T, choose some j∈U outside T, so its entry is zero. If all entries of U agree they must equal zero; if they do not, the definition returns zero. There can therefore be no *positive* common symbol.

Because the raw bound is a minimum of per-column capacities and `phi_C(U)<=ell-1`, appending this column yields the **literal identity**

`phi_(C ++ [a_(T,n)])(U) = min(phi_C(U), ell-1-n)` if U⊆T,
and `phi_C(U)` otherwise.

This is exactly `trackFCodingRaw d ell phi_C T (ell-1-n)`, **not an assumed age-level equality**. There is no bounded-support assumption on T; U always ranges over the actual support domain.

## Derived finite geometric-dictionary consequences

(A) **Age change.** Suppose `G_(phi_C)=F` and `F'⋖F` is a genuine integer graph-age cover. Let T be its unique minimal changed support. By the now-verified parts (1)–(3) of `Lem:Consecutive`, `F(T)=F'(T)+1`, and positivity plus `F(T)<=ell-1` imply `n=ell-1-F'(T)` is an integer between 1 and ell-2. Appending literal column `a_(T,n)` gives raw cap `ell-1-n=F'(T)`. The already merged `trackFRawCoverColumn_exact` then proves `G_(phi_new)=F'`.

(B) **Controlled-coding surviving column.** After removing coded branch j, let `phi_C` be the raw bound of the surviving equal-length words, and let `F=G_(phi_C)`. If every nonempty admissible U⊆X (X the passing-one set of survivors) satisfies `F(U)<=ell-2`, then appending the literal 1/0 column `a_(X,1)` leaves `G_phi` and all normalized feasible clique vectors unchanged by the merged `trackFCodingColumn_canonical_eq` and `trackFCodingColumn_feasible_iff`.

The second statement still requires a **deletion/restriction bridge** identifying `G_(phi_C)` with the old graph age restricted to the surviving coordinates; the literal E/passing-one equivalence and the minimal-pre-age admissibility clause remain separate obligations. Do **not** upgrade the full diary-bijection marker from these local results.

## Adversarial cases and proof pitfalls

1. The representative `r(U)` only exists because U is *nonempty*. It is erroneous to define the raw common-letter maximum on all subsets including empty without a convention.
2. The column `a_(T,n)` is not an arbitrary word transformation. It writes *one common positive symbol* on precisely the designated branches. A mixed 0/n column does **not** impose the positive bound on the entire mixed support.
3. A new column with `n=0` is vacuous. The age-change inference requires `1<=n<=ell-2`; the general raw formula itself remains correct if one treats zero separately.
4. The column representation must preserve the *chronological order* of letters, although computing `phi` itself is invariant under permuting columns. Diary identity and its inverse are **not** determined by `phi` alone (the 41-to-17 binary-shadow collision already documents this).
5. Before applying the cover theorem, `phi_C` may have raw slack `phi_C != G_(phi_C)`. Previous Track F PR #105 formally preserves this distinction; replacing `phi_C` by its canonicalization is not allowed at the definition stage.
6. The allowed alphabet `{0,...,ell-2}` ensures positive graph-age values. Formalize the raw column algebra for `Nat` first and impose the alphabet bound in the derived diary event theorem; no artificial assumption about `d` or `|T|`.
7. The *age-change critical support* is the unique minimal changed T of an actual cover. The raw column lemma alone is true for arbitrary T but does not prove unique decoding from the binary shadow.
8. Nothing here proves relative numerical-H L+ source assignment, corrected B3 microlevels, labelled inverse-source orbit, independent infinite unavoidability, or even the full concrete↔abstract diary bijection.

## Lean targets / acceptance

Implement a new `Kk/TrackFLiteralWordColumns.lean` with the actual list-of-columns model:

- `trackFColumnRepresentative_mem`
- `trackFNewColumnCommon`
- `trackFWordRaw_append`
- `trackFWordRaw_append_as_coding_cap`
- `trackFWordRaw_age_cover_exact`
- `trackFWordRaw_coding_preserves_age`

Check a concrete finite regression independently, then targeted `lake build Kk.TrackFLiteralWordColumns`, exact named standard-only axiom reports, and the full repository build at the final PR head. A theorem about the raw chronological words must use the actual column-based function, not assume the post-column cap as a hypothesis.
