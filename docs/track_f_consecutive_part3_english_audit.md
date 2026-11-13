# Track F — shortened proof of graph-age cover lemma, part (3)

**English-first adversarial audit, 13 November 2026.** This is a **separate mathematical proposal**, not yet marked Lean-verified. It targets manuscript `Lem:Consecutive`, part (3): for a genuine immediate cover `F'⋖F`, every changed support `U` satisfies `F(U)=F(T)`, where `T` is the unique inclusion-minimal changed support.

## Existing verified or staged inputs

- `Kk/IntegerAgeLocality.lean:integerGraphAgeCanonical_single_bound_locality`: reducing a *single raw bound* at support `S` leaves the canonical age at `T` unchanged whenever every nonempty support in `S∩T` has original age at most the new cap.
- `Kk/IntegerAgeSmallFunction.lean:integerGraphAge_monotone`: true integer-witness graph ages are support-monotone.
- `Kk/CanonicalCoverBlock.lean:AgeCover`: true cover/no intermediate age interface.
- Track F [PR #116](https://github.com/janhubicka/lean-kk/pull/116): **proposed** existence/uniqueness of the minimal changed support. (Its targeted build passed after a Mathlib API patch; full exact-head gate is a separate condition.)
- Track F [PR #119](https://github.com/janhubicka/lean-kk/pull/119): **proposed** one-step drop for every changed support, using a genuine normalized-clique witness. (Lean exact-head verification pending at writing.)

## Proof

Fix `F'⋖F` a genuine cover, and write `T` for the unique inclusion-minimal nonempty support with `F'(T)<F(T)`. Let `U` be **any** support with `F'(U)<F(U)`.

**First, T⊆U.** Because there are finitely many admissible supports, the collection of changed nonempty supports `S⊆U` has a member of least cardinality. Such an S is globally inclusion-minimal among changed supports: any changed proper subset would also be contained in U and have fewer elements. Uniqueness forces S=T, so T⊆U. (This does not require that T itself is the smallest by size among *all* changed supports, only uniqueness of inclusion-minimal changed supports.)

Put `n=F'(U)`, and let `B` be obtained from **F** by lowering **only** the raw U-bound to n, i.e. `B(V)=min(F(U),n)` when V=U and `B(V)=F(V)` otherwise. Since `F'≤B≤F`, the canonical age `H=G_B` exists, is genuine, and satisfies `F'≤H≤F`; because `H(U)≤n=F'(U)<F(U)`, we have H≠F. The cover property gives H=F'.

Suppose for a contradiction that `F(T)≤n`. For **every** nonempty admissible `V⊆U∩T`, monotonicity yields `F(V)≤F(T)≤n`. Apply the **verified one-support canonical locality theorem**, with reduced support S=U, retained support T=T, and cap n: the entire change at U **cannot affect the age at T**, so `H(T)=F(T)`. Since H=F', this contradicts `F'(T)<F(T)`.

Consequently `F(T)>n=F'(U)`. On the other hand, T⊆U implies `F(T)≤F(U)`. By part (1) of the cover lemma, which must be supplied from its separately verified proof, `F(U)=F'(U)+1=n+1`. Natural-number integrality therefore forces `F(T)=F(U)`, as desired.

## Adversarial checks

1. **Part (1) is really used.** The conclusion `n<F(T)≤F(U)` gives equality only because the cover's U-capacity drop is exactly one.
2. **At-most-one versus equality:** At a changed support U, `F'(U)<F(U)≤F'(U)+1` implies the exact identity `F(U)=F'(U)+1` over natural values; no separate stronger hypothesis needed.
3. **The original upper age must be genuine.** Monotonicity and the one-support locality theorem are false for arbitrary uncanonical raw vectors.
4. **The raw restriction is to U alone.** The literal *word* age-change column lowers all subsets of U, but `integerAgeLowerAt` here is the auxiliary *one-support* raw restriction; its canonicalizer must still be shown to equal F'. Do not substitute the two raw functions as syntactically equal.
5. **No falsely assumed support containment.** T⊆U is proved from finite minimization and uniqueness, not from an arbitrary poset cover axiom alone.
6. **Small support scope:** `IntegerGraphSupport d ell` excludes the empty set. A possible empty intersection gives vacuous locality hypotheses, already covered by the verified theorem.
7. **No global diary claim.** The result concerns a **finite integer-witness cover**. Its conclusions do not directly classify corrected-(B3) source microlevels or a new global infinite lower bound.
8. **Manuscript text policy:** black prose remains untouched. If an English revision is needed it belongs in Track F's separate note and eventual Track G integration, not a silent rewrite of `kk.tex`.

## Next formalization

A safe modular approach first proves, *with explicit containment*, the locality-based short conclusion:

```
(hCover : AgeCover (IsIntegerGraphAge d ell) lower upper)
(hTchanged : lower T < upper T)
(hUchanged : lower U < upper U)
(hTU : T.1 ⊆ U.1)
(hDrop : upper U = lower U + 1)
⊢ upper T = upper U
```

This uses only the already verified `integerGraphAgeCanonical_single_bound_locality`, canonicalizer max properties, and true cover. Then combine it with the finite support-minimization/uniqueness in PR #116 and the uniform one-step theorem from PR #119. Require exact-head build/axioms before declaring manuscript `Lem:Consecutive` complete.
