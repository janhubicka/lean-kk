# Track F: literal concrete edge predicate versus abstract passing bit (two surviving sorts)

**English first — 14 November 2026.** This proof is anchored to the real finite integer-witness K_ell age, literal chronological columns and the FULL word predicate E, including its distinct-word, initial 1, top-symbol and greatest-individual-common-symbol clauses. The theorem is not stated for arbitrary unsynchronized histories: the omitted-hypothesis counterexample K4 words (1) and (2) is genuine. It does not claim the full diary correspondence or independent BRD lower bound.

## Literal equal-length edge predicate

A finite level of two distinct active branches x=0 and j=1 is a chronological list of columns `cols : List (Fin 2 -> Nat)`. Let `Seen(i,n)` mean that some chronological column has symbol n at branch i. Define `E(cols,ell)` as the conjunction of:

1. The two equal-length word sequences differ at some coordinate.
2. `Seen(0,1)` and `Seen(1,1)`.
3. `Seen(0,ell-2)` or `Seen(1,ell-2)`.
4. There exists a **greatest** positive natural symbol n seen **individually by both** branches, and no chronological column has symbol n on both branches simultaneously.

This faithfully unpacks the manuscript's `E(u,v)` at equal-length active levels; the original prefix convention is irrelevant because both branches are active at the same level. Use an explicit greatest-symbol condition, **not** `min(maxSeen0,maxSeen1)` as a definition on arbitrary histories: that formula requires initial segments.

## Valid-diary branch-spectrum hypothesis

Let ell≥3. Assume branch x=0 has exactly the positive symbols `{1,...,a}`, and the proposed coded branch j=1 exactly `{1,...,ell-2}`, with `a≤ell-2`. This is precisely the positive-spectrum synchronization invariant being verified in Track F PR #156, specialized to `F({j})=1`.

Under those assumptions, the largest positive symbol individually seen on both branches is a (when a>0). The first three clauses of E are automatic for a>0. The non-simultaneous clause is exactly:

`there is NO column with col(0)=col(1)=a`.

Hence E iff `0<a` and no simultaneous occurrence of a.

Let `c` be the literal `trackFWordMax` on the full two-sort support, i.e. the greatest **simultaneously** common positive symbol. Every such symbol is one seen on x, so c≤a. If a>0, the absence of simultaneous a is equivalent to c<a. If a=0, both E and c<a are false. Thus, without any hidden extra assumption,

`E(cols,ell) iff c < a.`

Prove the latter using the exact finite-fold maximum, not a cardinal-only shortcut. An auxiliary lemma says `foldl max 0 < a` iff `a>0` and **each** common-symbol column value is below a; a simultaneous a makes the fold ≥a.

## Connection to the actual integer graph-age canonicalizer

Let `F=integerGraphAgeCanonical 2 ell (trackFWordRaw 2 ell cols)`. Assume F is a **genuine graph age** and the two branches have positive spectra synchronized with their genuine singleton ages as in `trackFWordSpectrumMatches`. Assume the proposed coded branch j=1 has `F({j})=1`.

Set `a=ell-1-F({x})` and `c=trackFWordMax(cols,{x,j})`. Genuine positive age bounds give `0≤a≤ell-2`. Synchronization yields exactly the required initial spectra on x and j.

The independently verified `trackFPair_word_capacity` gives

`F({x,j})=min(ell-1-c,F({x})+F({j}))=min(ell-1-c,ell-a)`.

The verified natural arithmetic lemma `trackFPair_passing_arithmetic` identifies

`F({x,j})=F({x})+1 iff c<a`,

using c≤a (from initial spectra) and `F({j})=1`. Combining with the literal E lemma gives the genuine two-sort theorem

`E(cols,ell) iff F({x,j})=F({x})+1.`

This is a fully concrete ↔ abstract *passing-one-bit* identity for the two selected branches, under the exact valid-diary synchronization hypotheses.

## Adversarial scope and counterexamples

- **Do not omit the initial segments.** K4, x=(1), j=(2) gives raw/canonical singleton ages 2 and 1, pair age 3. Thus the abstract test is true, E false, because j has never seen 1.
- **Do not omit genuine positive ages.** For unrestricted raw words canonicalization can give a singleton value zero; then a may be ell−1 and the word-level positive alphabet assumptions fail.
- **Do not omit distinct-word clause.** It is part of the manuscript's E; under c<a it follows automatically, because x actually sees a somewhere and j cannot see that symbol at the same column, but the proof must show it.
- **Do not silently identify the two different maxima.** The greatest symbol seen individually by both branches is a only under *both* positive-initial-segment assumptions. The greatest simultaneously shared symbol c is a different quantity.
- **Do not mistake pairwise bit equality for full controlled coding.** The all-subsets cap condition and the minimal-pre-age clause must still be checked. The safe coding age-preservation theorem in merged PR #139 explicitly assumes the cap.
- **Do not assume arbitrary word lengths.** Both words here come from a single level of equal-length chronological columns. The prefix version of E for coding nodes of different lengths remains another diary step.
- **Do not claim all-size dictionary from two sorts.** Arbitrary distinct branches of a larger level require injection/reindexing, already verified in PR #139, followed by an explicit invariance of the word E predicate under coordinate selection.
- **Do not green-mark independent unavoidability.** This is a finite local dictionary identity and says nothing about infinite persistence of types.

## Lean acceptance targets

Use two modules if it improves audit:
- `Kk/TrackFWordEdgeLiteral.lean`: literal E definition; `trackFWordEdge_iff_no_simultaneous_top`, `trackFWordMax_pair_lt_iff`, `trackFWordEdge_iff_commonMax_lt`.
- `Kk/TrackFWordEdgePassing.lean`: `trackFWordEdge_iff_abstractPassing` using the *actual* normalized canonical age, `trackFPair_word_capacity`, `trackFPair_passing_arithmetic` and genuine spectrum synchronization.

Use exact-head explicit module builds and named standard-only transitive axiom reports. Black manuscript prose, `validation.tex`, central Kk Lean registry and global diary validation markers remain untouched.
