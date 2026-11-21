# Track F — every genuine finite Henson type front has a genuine canonical graph age

21 November 2026. English proof and adversarial audit **before Lean**. Application to the pre-code profile rigidity theorem merged in lean-kk PR #430. This is an actual chronological one-type statement, not an auxiliary Kpt profile.

## Statement

Fix any `ell≥2`, a genuine (possibly non-symmetric) directed ordinary graph table E, and a finite family `u_i : HensonOneType(ell,E)` indexed by `Fin(d)`, all at one common chronological old level H. No injectivity of the family, global left density, or rank-large coding fibre is required.

Let `B(T)=trackFCommonRawAge(d,ell,H,E,(N(u_i)),T)` be the **actual** old common-neighbour clique-capacity RAW bound for each nonempty admissible support T (support size≤ell−1). Define `P=integerGraphAgeCanonical(d,ell,B)` using the verified normalized integer-witness canonicalizer.

**Conclusion:** `IsIntegerGraphAge(d,ell,P)`: the complete canonical finite sorted-graph profile of the actual front is a genuine integer graph age.

## Proof

Each genuine one-type u_i carries the exact safety proof that its positive old-neighbour set N(u_i) has directed clique capacity strictly less than ell−1. Because every neighbour is below the type's level H, the actual common old-neighbour pool on a nonempty support T is a subset of N(u_i) for ANY i∈T. Hence its directed clique capacity is at most the safe singleton capacity and is therefore strictly below ell−1. It follows that

`B(T)=ell−1−cap_E(commonNeighbourPool(T)) ≥1`

for EVERY admissible nonempty support, including all mixed pairs/triples.

The already verified constant-one normalized integer graph-age function (`integerGraphAge_const_one_is_age`, module `Kk.FiniteOldColumnAgePositive`) is genuine for ell≥2. The all-support positivity above gives `AgeLe (fun _ =>1) B`. Apply the verified greatest-age canonicalization theorem `integerGraphAgeCanonical_is_age` to conclude `IsIntegerGraphAge(d,ell,G_B)`.

There is no assumption that the RAW B itself is canonical or an age; the canonicalizer is essential. The proof uses genuine clique CAPACITY of the full common old-neighbour pools, not cardinality of raw intersections.

## Adversarial audit

1. Each u_i must be a **genuine safe** HensonOneType, not an arbitrary finite positive-neighbour list. If a neighbour set contained an (ell−1)-clique, the singleton RAW bound would be zero and positivity could fail.
2. The positive old-neighbour set of each u_i is entirely below its own `level`; the common level H is needed to align the RAW prefix definition.
3. The support is NONEMPTY, so one can select i∈T. The empty support cannot be used to force positivity by this argument.
4. Monotonicity of directed clique capacity under subset inclusion works for true graph E without imposing undirected symmetry.
5. The raw bound is `ell−1−cap` with Nat subtraction. Strict `cap<ell−1` implies result ≥1, avoiding accidental saturation at zero.
6. No `d≥1` hypothesis: when d=0 there are no nonempty supports, and all statements are vacuous. No invented Fin(0) witness.
7. The bound `T.card≤ell−1` is the actual `IntegerGraphSupport` domain. The proof does not rely on a larger unrestricted support family.
8. Positivity on each singleton implies positivity on all mixed supports because common-neighbour pools shrink as supports grow. We explicitly prove the genuine pool subset, rather than asserting positivity by naming it.
9. The constant-one witness age is already kernel-checked. The proof does not assume the canonicalizer preserves positivity without a lower genuine age.
10. This is the true *physical* RAW function `trackFCommonRawAge`, not a selected shadow or an unverified diary age.
11. No source/target compatibility, induced embedding or self-copy is used; it applies equally to target prefix tuples at an arbitrary intermediate code cut.
12. Therefore it discharges precisely the `IsIntegerGraphAge P` hypothesis of the zero-code preprofile rigidity #430 **once P is identified with that actual intermediate canonical profile**. Such identification and the survivor-profile sandwich remain separate history obligations.
13. No claim of numerical raw equality with the canonical bound: redundant raw inequalities may disappear during canonicalization.
14. No claim of full Kpt E/parameter/B3 profile, diary unavoidability or exact BRDs.
15. Frozen black manuscript proof stays unchanged; only update its validation TODO after exact-head Lean and strict axiom gates pass.

## Lean validation

Prove a named all-support positivity theorem for the true `trackFCommonRawAge` computed from the neighbours of genuine same-level `HensonOneType`s, then the genuine normalized canonical integer graph-age theorem by `integerGraphAge_const_one_is_age` + `integerGraphAgeCanonical_is_age`. Both named statements must compile exact head and pass strict standard-only transitive-axiom checks.
