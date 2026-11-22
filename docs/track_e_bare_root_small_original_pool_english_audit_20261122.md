# Track E E90 — small physical root pool for an actual finite-old-seed / one-bare-new-original extension

**22 November 2026. English-first proof and 20 adversarial checks committed before Lean.**

## The correctly tailored root-cardinality bound

E89 (draft PR #499, source gate pending at the start of this note) proves that a finite family Y of true Kpt seed nodes represented by numerical-H+ originals from U admits a SMALLER valid root-original pool U₀⊆U of size at most |Y|. The physical Kpt ancestor relation of each seed is preserved literally.

But the actual Track E whole-run theorem E84 adds ONE COMPLETE bare physical original O_new with a SPECIFIED original address newV. It requires `newV∈U`. An arbitrary choice of root representatives for the entire new seed family Y need not retain that particular name when different physical originals realize the same complete Kpt original type.

The correct one-bare-root construction is therefore:

1. Begin with the finite OLD INITIAL seed family `X₀:Finset(KptNode)`, represented in actual `ambientPrefixPool(A,U)`, where |X₀|=m. Its elements may include legitimate dependent Kpt nodes; no all-old-seeds-are-originals shortcut.
2. Apply E89 root compression to **OLD seeds only**. Choose U₀⊆U with |U₀|≤m representing every old seed.
3. Define `U' = U₀ ∪ {newV}`. Because newV∈U, we have U'⊆U; also |U'|≤m+1. Crucially newV∈U' by construction.
4. Let `Y=(X₀:Set KptNode)∪{A.kptOriginal(newV)}`. Old seeds remain represented by U₀⊆U', while the added complete bare root is represented by itself with actual original name newV∈U'. Hence Y⊆ambientPrefixPool(A,U').
5. A true OLD AlgorithmRun R on X=(X₀:Set KptNode) is unchanged. The candidate new source is computed from Y and R.I(c+1), never from a new Y-run or a guessed selected graph-age Plan.

Thus the EXISTENCE of a common physical root pool with size ≤m+1 is proved without assuming the old Kpt seeds are literal originals.

## Theorem E90.1 — actual one-bare-root pool compression

For any finite numerical-H+ structure A avoiding the normalized Kpt family, finite old Kpt seed Finset X₀ represented by U, and newV∈U, there exists a true U'⊆U such that

    newV∈U',
    U'.card ≤ X₀.card+1,
    ((X₀:Set KptNode)∪{A.kptOriginal(newV)}) ⊆ ambientPrefixPool(A,U').

No assumption that `kptOriginal` is injective, that newV is uniquely determined by its type, or that the old seed family contains no dependent parameters enters the proof. U' is a NEW chosen bookkeeping pool; it is not asserted to be the same as the old U.

## Theorem E90.2 — maximal OLD-prefix tests for this compressed one-root presentation

Fix one genuine OLD AlgorithmRun R on X=(X₀:Set) to top h and any Allowed source cuts. E86 applies to the same complete candidate new seed set Y, but with the newly chosen U' as its genuine physical original-name representation. It gives

    Need(U').card ≤ U'.card + |SelectedOld(R)|
                  ≤ X₀.card+1 + |SelectedOld(R)|.

This is independent of the new physical numerical-H+ carrier N and the number of boring numeric gaps. The at-most-one additional root name exactly reflects the true bare new root, not an unbounded list of its ancestors.

This is a stronger application-facing finite-stage budget than E86's original |U|+selected bound WHEN the prior root pool U was padded relative to a finite old seed set.

The theorem counts distinct ACTUAL maximal original OLD Kpt prefix TESTS for the chosen compressed root pool, not physical bad CUTS, and says nothing about whether the old prefix witnesses are available.

## Relation to uniform diary bounds

If the actual old seed set X₀ has cardinality controlled by the abstract fixed diary, then the only remaining counting term is the number of genuine old selected source levels. A diary-uniform bound on that second term, plus the existence of old-prefix witnesses and control of unsafe physical cut classes, would be needed before one can infer a uniform source-carrier budget. None of these is automatically supplied by E90.

The chosen U' need not preserve unrelated hypotheses involving ALL original names in U (e.g. requirements to include an entire original-Q block). Any use of the compressed representation in the resolved-Q induction must check those role/Plan assumptions separately. Properties universally satisfied by every element of U are inherited by a subset, but “all designated names must be present” is not.

## Hostile checks (20)

1. Old X₀ is an explicitly finite Finset of ACTUAL initial Kpt seed nodes.
2. Old X may contain dependent parameters and non-original prefixes.
3. The old root pool U represents every seed as a literal Kpt prefix of an actual original in A.
4. The new seed is exactly ONE complete bare original O_new with specified name newV∈U.
5. E89 compression is applied ONLY to old seeds, not to Y with an arbitrary chosen representative of O_new.
6. newV is explicitly reinserted in U'=insert(newV,U₀).
7. U'⊆U follows because both U₀⊆U and newV∈U.
8. Cardinal bound |U'|≤|U₀|+1≤|X₀|+1 remains sound even if newV∈U₀.
9. No claim that `kptOriginal` is injective is used.
10. Actual Kpt ancestor relations, including dependent E and negative L bits, are preserved for old seeds.
11. O_new is represented literally by itself at the chosen newV name.
12. The NEW initial seed set Y does not contain all lower ancestors of O_new as additional seeds.
13. Changing bookkeeping original pool U to U' does not change old source X, new seed Y or physical closure at old R.I(c+1).
14. E86's Need support MUST be recomputed for the chosen U', not silently identified with Need(U).
15. E86's selected-old cardinal includes top; no strict q<h replacement.
16. Original old root pool U may be arbitrarily padded, and the theorem does not force |U|≤|X₀|+1.
17. E90 is a finite-stage existence result, not an assertion that an already fixed chronological Q Plan continues to hold after dropping original names.
18. Old seed cardinal |X₀| may still grow with the physical realization; no diary-uniform bound is inferred without separate control.
19. Full old-prefix witness existence, unsafe odd/nonzero physical cut classes and K4 E/q2 cuts remain.
20. Cross-occurrence source-coordinate normalization, assigned successor characters, common labelled inverse-source monoid orbit and upper/sharp BRD remain open.

## Formalization gate

E90 is stacked on E89's source branch until the latter passes its own exact-head direct Lean + strict two-name axiom gate and independent full build, and is merged. Formalize: (1) root pool U'=insert newV U₀ with literal old+bare new seed representation and |U'|≤X₀.card+1; (2) the E86 maximal-original test budget on U' with the same true old R. Use only verified Finset cardinal and `ambientPrefixPool_mono` APIs, keep U' versus U distinction explicit. Require E90's own dedicated named standard-only axiom checks, negative parser self-test and independent full Lean build before merge. No frozen black manuscript edits or global BRD validation promotion.
