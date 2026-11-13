# Track F: existence and uniqueness of the essential changed support of a genuine K_ell graph-age cover

**English proof and hostile audit before Lean**, continuing the independently checked raw age-cover bridge in merged [PR #105](https://github.com/janhubicka/lean-kk/pull/105) and the older `integerGraphAgeCover_minimal_changed_unique` theorem in `IntegerAgeCoverSupport`.

## Precise statement

Let `ell>0`, let the active sorted coordinates be `Fin d`, and let `F'<F` be a **genuine immediate cover** in the actual normalized finite integer-witness K_ell graph-age poset, i.e. `AgeCover (IsIntegerGraphAge d ell) lower upper`.

Then there exists **exactly one** admissible nonempty support `T` such that

1. `lower(T)<upper(T)`, and
2. for every other admissible nonempty support `U` strictly contained in `T`, `lower(U)=upper(U)`.

This is the **existence plus uniqueness** part (2) of manuscript `Lem:Consecutive`, which previously only had the *at most one* Lean theorem.

## Proof

1. Because `lower ≠ upper`, there is some admissible support U on which the functions differ (functional extensionality). Since `lower≤upper` pointwise, such a difference necessarily satisfies `lower(U)<upper(U)`. Hence the finite set `C` of changed supports is nonempty.
2. The support type is finite: it is a subtype of the finite powerset of `Fin d`. Consider the finite **nonempty** set of natural cardinalities `{|U|:U∈C}`. Let `m` be its minimum and choose a changed support `T` with `|T|=m`.
3. If a proper admissible nonempty `U⊊T` were also changed, then `|U|<|T|=m`, contradicting minimality of m. Thus T is inclusion-minimal among changed supports.
4. If S is any other inclusion-minimal changed support, the previously *fully Lean-verified* theorem `integerGraphAgeCover_minimal_changed_unique` applies to S and T (including their actual age and genuine-cover hypotheses) and gives S=T. So the support is unique.

No assumption about the complete numerical-H source, physical relative realization, B3 tests, or full diary exists in this argument.

## Hostile cases

- **Empty support is excluded.** The minimality argument runs over `IntegerGraphSupport d ell` (nonempty finite sets of cardinality at most ell−1), not all powersets including the empty set.
- **Finiteness is essential for the chosen minimum.** We do not generalize this to arbitrary infinite supports or infinitely many coordinates.
- **Strictness of the cover matters.** With `lower=upper` the changed set is empty; the theorem requires `AgeCover.strict`.
- **Pointwise order is essential.** A mere inequality of functions without `lower≤upper` would produce a difference but not necessarily a *decrease*.
- **Uniqueness is not a consequence of finiteness alone.** A general pair of ordered integer functions can have several incomparable minimal changed supports. The actual graph-age cover and existing canonical-locality lemma are essential to uniqueness.
- **No one-step drop yet.** This does not prove `upper(T)=lower(T)+1`; that is part (1) of manuscript `Lem:Consecutive` and remains a separate lemma. The concrete nonzero symbol `ell−1−lower(T)` requires that numerical bound.
- **No reduction of every changed support's upper value.** Part (3) of `Lem:Consecutive` remains separate.
- **Does not prove the diary inverse.** Identifying a unique essential support is necessary but not sufficient to reconstruct all splitting/coding age annotations.

## Proposed Lean module

`Kk/TrackFCoverEssentialSupport.lean`:
- `trackFCover_exists_minimal_changed`
- `trackFCover_unique_minimal_changed`

Use genuine `AgeCover (IsIntegerGraphAge d ell)` and the merged theorem `integerGraphAgeCover_minimal_changed_unique`. Explicitly compile and check named transitive axioms. Do not mark the full `Lem:Consecutive` or full diary correspondence green until parts (1),(3) and remaining steps are proved.
