# Track F: any coordinate of a genuine integer graph-age cover drops by at most one

**English proof and adversarial audit, written before Lean.** This is manuscript `Lem:Consecutive` item (1) in the actual normalized finite K_ell graph-age model, not just a numerical regression. The previously verified `diaryCoverColumnCanonical_exact` and `trackFRawCoverColumn_exact` *assume* a genuine cover but do not establish the step size.

## Theorem

Let `F'<F` be a proper immediate cover in `IsIntegerGraphAge d ell`, with `ell>0`. For **every** admissible nonempty support T, `F(T) <= F'(T)+1`. In particular, at any changed T, `F(T)=F'(T)+1`.

This justifies the **one-step** decrement needed to determine the legal nonzero age-change symbol `n=ell-1-F'(T)`. The actual symbol bound also uses the positive-age condition `1 <= F'(T)` and `F'(T) <= ell-2` when T changes.

## Proof

Fix a changed support T and let `k=F(T)`. Since F' has positive graph-age values and F'(T)<k, necessarily k>=2. Let `n=k-1`.

Define the single-support raw bound B by `B(T)=min(F(T),n)=n`, and `B(U)=F(U)` for every other U. Then `F'<=B<=F` because F'<=F and F'(T)<=k-1. The canonicalization `H=G_B` is a genuine graph age: F' is a true age below B, so the verified actual integer-witness canonicalizer applies. It satisfies `F'<=H<=F`; the inequality `H(T)<=n<k=F(T)` forces H≠F. By immediate-cover minimality, `H=F'`.

Now take an actual normalized integer-clique witness w for F on T, so `w(T)=k` and w satisfies every support bound of F, with total multiplicity at most ell-1. Since k>0 there exists some coordinate i∈T with `w(i)>0`. Decrease just w(i) by one to produce w'. The new vector is still nonnegative, its total multiplicity remains at most ell-1, and every support sum is ≤ its original value, so it continues to respect F. On T its sum is exactly k-1=n, so it also respects B. Thus the canonical maximum H(T) is at least n. As H≤B and B(T)=n, we have H(T)=n. Combining H=F' gives F'(T)=F(T)-1.

At any unchanged support the asserted inequality is immediate; therefore F(T)≤F'(T)+1 for every admissible T.

## Adversarial cases

- **A genuine cover is essential.** If F' is strictly below F with an intermediate age, lowering one raw bound by one generally finds an intermediate age rather than the proposed F'.
- **Real witness is essential.** One may not decrement a formal capacity label without a feasible integer-clique witness. The normalized graph-age consistency axiom provides exactly that witness.
- **A positive T-coordinate exists.** The equality `sum_T w=k>0` implies a coordinate in T has positive weight. The proof must choose that coordinate; decrementing a zero coordinate does not change the total.
- **All support constraints survive.** Decreasing a single nonnegative multiplicity never increases any support sum, including supports overlapping or containing T and supports not containing T.
- **No artificial total-weight assumption:** Total ≤ell-1 is part of the actual normalized witness representation, equivalent to the paper's original unrestricted witness definition by an already verified theorem. Decreasing one coordinate preserves it.
- **No lower bound n=0:** For a *changed* T, the positive lower graph-age value F'(T)≥1 gives k≥2, so n=k-1≥1; the resulting canonical age remains within the positive-age domain.
- **Only cover-local:** This does not derive the unique minimal changed support or classify the other upper values of changed supports, and says nothing about H+ B3 or infinite Ramsey bounds.
- **Raw concrete words:** The conversion to literal raw word bounds, including slack B≠G_B, has been proved separately in merged PR #105.

## Lean plan

1. Prove a normalized **single-coordinate decrement witness** on `IntegerCliqueWeights d ell` with the chosen positive coordinate and exact T-sum decrement. Do not assume a stronger shortening operation as an axiom.
2. Apply the real `integerAgeLowerAt` and `integerGraphAgeCanonical` to show the new age lies between the cover endpoints; use the decremented witness to establish the new age's T-value exactly k-1.
3. Derive `F(T)<=F'(T)+1` for every support and equality at every changed support.

If the exact Lean proof is blocked, keep these precise sublemmas as TODOs; do not mark the paper's statement green from finite tests alone.
