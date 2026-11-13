# Track F — an exact *general* cover-column theorem (English first)

Status: mathematical proof and hostile audit written before `Kk/DiaryCoverColumn.lean`. This concerns **abstract sorted integer-witness graph ages**, not numerical-H source realization, (B3), an infinite resolved diary, or the independent big-Ramsey lower bound.

## Precise theorem

Fix `d, ell` and the finite support type `IntegerGraphSupport d ell`. Let `F'` and `F` be normalized integer-witness graph ages, with `F'` a **proper immediate predecessor** of `F` in the pointwise order (the Lean `AgeCover` interface). Fix **any** admissible support `T` such that `F'(T) < F(T)`. Define the raw all-subsets column bound

`B(U) = min(F(U), F'(T))` if `U subseteq T`; `B(U)=F(U)` otherwise.

Then the **actual integer-witness canonicalization** satisfies `G_B = F'`. Thus a normalized labelled clique multiplicity vector is feasible for `B` if and only if it is feasible for `F'`.

This theorem needs **no assumption that T is minimal among changed supports**: the latter is a separate uniqueness requirement for reconstructing the *particular* diary age-change column. It also does **not** assert that a physical numerical-H source realizes the bound.

## Proof

1. The lower age is below B. Outside T this is the cover inequality `F'<=F`. For each nonempty U subseteq T, monotonicity of the genuine graph age `F'` gives `F'(U)<=F'(T)`; combine with `F'(U)<=F(U)` to get `F'(U)<=B(U)`.
2. By integer-witness canonicalization, `G_B` is a genuine age, `F'<=G_B<=B<=F`.
3. Since `B(T)=min(F(T),F'(T))=F'(T)<F(T)`, it is impossible that `G_B=F`.
4. As `F'` is an immediate predecessor of `F`, no genuine age lies strictly between. Therefore `G_B=F'`.
5. The separately verified canonicalization property says that a normalized integer witness satisfies all of `B`'s inequalities iff it satisfies those of `G_B`, hence those of `F'`.

## Adversarial checks

- **Avoid silently replacing cover by strict inequality.** If an intermediate age exists, step 4 fails: the canonicalized bound may lie strictly above F'. Example: a one-sort K4 graph age F=3 and F'=1 with T its singleton gives raw bound 1, so G_B=1 here, but other multi-sort examples can leave intermediate ages; the cover hypothesis is essential to *this proof*.
- **Need genuine age monotonicity.** Pointwise `F'<=F` alone does not establish `F'(U)<=F'(T)` for subsets U of T; it follows from the genuine normalized integer-witness definition and its previously Lean-verified monotonicity theorem.
- **No claim about unique T yet.** If more than one changed support is chosen, the same canonical target could arise by different raw restrictions. The existing `integerGraphAgeCover_minimal_changed_unique` proves *at most* one inclusion-minimal changed support, using the genuine graph-age structure; existence still requires finite-support minimization.
- **No special singleton exception.** The proof works when T is a singleton (the new nonzero symbol may record a singleton age decrease), and when T is higher-dimensional.
- **No false equivalence of raw functions.** The raw B is generally **not equal** to F': its canonicalizer is F'. The theorem proves exactly that; a missing equality `B=F'` must not be inserted.
- **No edge/colour geometric conclusion.** This theorem does not prove the controlled-coding passing-one set, terminal-edge preservation, inverse to binary-shadow erasure, or the entire general diary bijection.
- **No cardinal-only proof.** The case `F'(T)=F(T)-1` is not even necessary for the canonicalization result; it is supplied separately by the true Hasse-cover classification when deriving the concrete symbol `ell-1-F'(T)`.

## Existing formalization reused

- `Kk.IntegerWitnessCanonical`: `integerGraphAgeCanonical_is_age`, `integerGraphAgeCanonical_le_raw`, and `integerGraphAgeCanonical_greatest`
- `Kk.IntegerAgeSmallFunction`: `integerGraphAge_monotone`
- `Kk.CanonicalCoverBlock`: exact `AgeCover` structure
- `Kk.IntegerAgeUniversalProperties`: `integerGraphAgeCanonical_preserves_clique_vectors`
- `Kk.IntegerAgeCoverSupport`: separate minimal-changed-support uniqueness proof

**Verification gate:** require compilation of the new module at its exact commit and a strict standard-only `#print axioms` report. Do not mark `Lem:Concrete_Abstract_Correspondence` green from this sublemma.
