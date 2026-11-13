# Track F: controlled-coding column preserves the **actual** abstract graph age

**English proof and adversarial audit, written before Lean.** Companion to the merged Track F cover-column and labelled-fibre results ([PR #101](https://github.com/janhubicka/lean-kk/pull/101)). Scope: an exact *finite raw-bound to canonical-age* argument for the graph-age change at a controlled coding level. This is not yet the whole abstract/concrete diary bijection.

## Statement — arbitrary raw slack, arbitrary support set

Let `d,ell` be natural numbers and `X` any subset of the `d` sorted coordinates (in particular, `X` may have size larger than `ell-1`). Let `B` be an **arbitrary raw bound** on all nonempty supports `U` with `|U|<=ell-1`, and let `F=G_B` be its normalized integer-witness canonical graph age. Assume the true age `F` is admissible, and that for **every admissible nonempty support** `U subseteq X`, `F(U)<=n`.

Define the raw bound obtained after writing the same new nonzero symbol on precisely the surviving branches in `X`:

```
B_X,n(U) = min(B(U),n)    if U subseteq X
         = B(U)           otherwise.
```

Then **`G_(B_X,n)=F`**, and `B_X,n` admits exactly the same normalized labelled clique vectors as `B`. In the concrete K_ell coding step the new symbol is 1, so `n=ell-2`. The actual controlled-coding hypothesis from Example 3.2.3 requires `F(U)<=ell-2` for every nonempty admissible `U subseteq E_j`, exactly this hypothesis.

The theorem is conditional on having already *removed the coded coordinate j* and identified the restricted canonical age with F. It does **not** prove that deletion/relative restriction preserves age: that is a separate remaining correspondence sublemma.

## Proof

1. By the defining greatest-age property, `F=G_B <= B` pointwise. If `U subseteq X`, the hypothesis also gives `F(U)<=n`, so `F(U)<=min(B(U),n)=B_X,n(U)`. Otherwise `B_X,n(U)=B(U)`. Hence `F<=B_X,n`.
2. Since `F` is a genuine age below `B_X,n`, the canonicalizer produces a genuine graph age `G_(B_X,n)`, with `F<=G_(B_X,n)`.
3. The new raw bound satisfies `B_X,n<=B`, so `G_(B_X,n)<=B`. Maximality of the original `G_B=F` among all genuine ages below `B` gives `G_(B_X,n)<=F`.
4. Both inequalities imply `G_(B_X,n)=F`. The existing canonicalization-preserves-feasible-vectors theorem gives `Feasible(B_X,n,w) iff Feasible(G_(B_X,n),w) iff Feasible(F,w) iff Feasible(B,w)`.

## Hostile tests and explicit counterexamples

- **Raw vs canonical:** Usually `B != F`. The theorem works with arbitrary raw `B`, not merely `B=F`. Proving a trivial equality after replacing raw `B` by the canonical `F` would *not* justify concrete words whose raw bound is noncanonical.
- **Necessity of every subset:** It is not enough to check `F(X)<=n` if `X` is outside the support domain, e.g. `|X|>ell-1`. The correct quantifier is over **all** admissible nonempty `U subseteq X`. If `X` is within the domain then monotonicity makes checking its top support sufficient, but our statement avoids this size assumption.
- **Cap failure actually changes age:** In `K_4` with a single active sort, `B({0})=3`, `F({0})=3`, `X={0}`, and `n=2`, the new canonical age has value 2. The `F(U)<=n` premise is indispensable.
- **`X=empty`:** No nonempty support lies within X. The new raw bound is literally B and the theorem applies vacuously.
- **Empty support excluded:** Do not introduce `U=empty` into `IntegerGraphSupport d ell`; the concrete raw-bound domain excludes it and the empty-set value is merely a harmless convention when needed for formulas.
- **One-directional passing bits:** The age preservation theorem is agnostic about the edges. One still must prove that the word-based `E` predicate agrees with the controlled-coding set `E_j={x != j: F({j,x})=F({x})+1}`. A compatible binary relation is not produced by this theorem.
- **Deletion is not harmless by fiat:** The remaining-coordinate canonical age should be the genuine *restriction of the graph age* after coding j. It must be shown to equal the canonical age computed from the raw bounds of the surviving concrete words **before** appending the passing bits.
- **No B3/orbit conclusion:** Neither numerical-H parameter-closed (B3) nor the full infinite lower bound is affected.

## Lean endpoints

`Kk/TrackFCodingColumn.lean` uses `IntegerGraphSupport`, `IsIntegerGraphAge`, `integerGraphAgeCanonical`, `AgeLe` and the actual `integerGraphAgeCanonical_preserves_clique_vectors` theorem. Intended checked declarations:

- `trackFCodingRaw_le_original`;
- `trackFCodingColumn_canonical_eq`;
- `trackFCodingColumn_feasible_iff`.

No `sorry`, `axiom`, `admit`, postulated Ramsey hypothesis or replacement graph-age interface. Confirm an exact-head targeted build, the complete repository build and named standard-only transitive axiom reports before calling them verified.
