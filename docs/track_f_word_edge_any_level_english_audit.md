# Track F — lift faithful two-word E/passing equivalence to arbitrary active levels

**English-first adversarial audit**, stacked on [Track F literal two-word E PR #162](https://github.com/janhubicka/lean-kk/pull/162). This lift is not a separate Ramsey argument and must reuse the already Lean-verified arbitrary survivor-injection canonicalizer from PR #139. Black manuscript text, central validation registry and global correspondence marker remain unchanged.

## Exact setup

Fix ell≥3 and d active **equal-length** chronological concrete words `cols : List(Fin d -> Nat)`. Define `F=integerGraphAgeCanonical d ell (trackFWordRaw d ell cols)`, and assume F is a **genuine positive integer-witness K_ell graph age**. Assume the fully synchronized positive-initial-segment invariant, `trackFWordSpectrumMatches d ell h2 cols F`.

Fix two distinct ordered active sorts x≠j, with the prospective coded branch j satisfying singleton age F({j})=1. Define the genuine two-sort injection

`f : Fin 2 ↪ Fin d`, `f(0)=x`, `f(1)=j`,

and the projected chronological words `cols2=trackFRestrictColumns f cols`.

The actual general literal E(cols,x,j) is defined using *exactly* the manuscript's clauses, without mentioning F: the words differ at some coordinate, both saw symbol 1, at least one saw ell−2, and the **largest positive symbol seen separately on both** did not occur simultaneously. All symbols are read at the same chronological level.

## Proof that the two-sort theorem applies

1. **Faithful word restriction.** Every statement `Seen(cols2,i,n)` is equivalent to `Seen(cols,f(i),n)` by the actual list-map membership equivalence. A simultaneous symbol is likewise preserved, as is the existential "words differ" condition. Therefore `E(cols2,0,1) ↔ E(cols,x,j)`.
2. **Exact raw+canonical restriction.** The merged `trackFWordCanonical_reindex` proves that `F2=G_(raw cols2)` equals the exact pullback `F∘f_*` on *all admissible nonempty supports*. No assumption that raw word phi equals F is used.
3. **Age and synchronized spectrum restriction.** `trackFGraphAge_reindex` proves F2 remains a genuine graph age. Positive-symbol synchronization is transported branchwise along f, since singleton supports pull back to singleton supports and chronological seen-symbol predicates are preserved.
4. **Candidate code age.** The full singleton age of j is 1, hence the small canonical age of 1∈Fin 2 is also 1.
5. Apply the two-sort theorem `trackFConcreteEdgePair_iff_abstractPassing` from PR #162. It gives, after rewriting mapped pair/singleton supports,

`E(cols,x,j) ↔ F({x,j})=F({x})+1.`

This is the exact passing-bit equality needed in the coded-column case of the concrete↔abstract diary dictionary, **for any d,ell**, under the explicitly stated valid-diary spectrum synchronization premise.

## Adversarial obligations not discharged

- **Only branch injectivity, not just two numbered slots:** x≠j is essential to preserving distinct singleton supports and two-sort integer clique weights. The pair selection must be an actual `Fin 2 ↪ Fin d`, not an arbitrary map.
- **Lexicographic order vs selected order:** f lists (x,j), not necessarily ascending indices. The numerical graph-age equation and ordered pair of words are invariant under permuting the two branches; the full diary's linear order must still be verified when producing an abstract ordered tree.
- **Valid word-level distinctness:** the E predicate has its own word inequality, and the theorem detects it; it does not assume x≠j automatically forces different histories. If the entire words coincide, the largest common positive symbol necessarily occurs simultaneously and E is false.
- **No skipped symbols:** the branch-spectrum synchronization remains an explicit premise. Arbitrary histories such as K4 x=(1),j=(2) violate it and refute the conclusion.
- **No automatic controlled coding:** E↔X is only the pairwise passing-one rule. The all-subsets safe cap and complete minimal-pre-age condition are still required, as are non-free splitting and the full chronology-respecting inverse.
- **No independent BRD lower bound:** local finite edge equivalence does not prove unavoidability of every diary type.

## Lean endpoints

`Kk/TrackFWordEdgeAny.lean` should define the exact general literal `trackFConcreteEdgeAt`, the injection `trackFSelectPair`, show `trackFSeenSymbol_reindex`, `trackFConcreteEdgeAt_reindex`, and the spectrum preservation under injection, then conclude `trackFConcreteEdgeAt_iff_abstractPassing` on actual canonical word ages. Use targeted explicit module compilation and standard-only named axiom reports; keep the PR stacked until the two-word theorem and its exact-head checks are green.
