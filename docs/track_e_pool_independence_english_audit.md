# Track E continuation — physical closure crossings do not depend on the representing original pool

**Date:** 13 November 2026. **Scope:** one actual complete finite Kpt closure at one numerical H+ stage. English argument and adversarial checks prepared before Lean implementation. This is a *geometric* refinement of the integrated Track C/E interfaces, not a replacement for the missing across-occurrence common orbit.

## Main source-graph uniqueness lemma

Fix a genuine admissible Kpt tree, a **fixed actual closure set** `Z` of its nodes, and a cut `c`. Let `F,G` be two (B1/B2) prescribed full L+ crossing functions of source types at `c`. Assume BOTH of:

- **Cover:** every `z ∈ Z` of length (>c) has its precise old ancestor at `c` and its next ancestor at `c+1` represented by a source/target pair of each function (`CoversClosureCrossing`).
- **Graph:** every source/target pair appearing in either function is realized by the consecutive ancestors of some real `z ∈ Z` crossing `c` (`IsCrossingGraphOf`).

Then `F.source = G.source`, and their **complete upper L+ targets agree** at every element of this common source. This is literal equality of `PartialTypeWithE` records (including all ordinary directed L bits, negative bits, unary/diagonal data and auxiliary E); it is not equality of merely their ordinary L reducts.

**Proof.** Take `T∈F.source`. By Graph for `F`, find `z∈Z` whose complete old and next raw type nodes are `(c,T)` and `(c+1,F.target T)`. By Cover for `G`, the *same z* has corresponding `(c,U)` and `(c+1,G.target U)` for `U∈G.source`. Equality of raw Sigma-pairs at the same levels yields `T=U` and, substituting, `F.target T=G.target T`. This gives source inclusion and target equality. Interchange `F,G` for reverse inclusion. No arbitrary representative is identified: the result is independent of duplicate original names and of choice of a target representative.

## Physical finite numerical H+ consequence

Let `A=finiteNumericH K k N` be a fixed *actual* finite H+, whose ordinary L structure avoids the chosen normalized forbidden family. Let `Z` be a fixed complete closure and suppose there is **no competing (I2) meet at cut c**. Take two arbitrary finite original-name maps `original₁ : Fin M₁ → Fin A.size` and `original₂ : Fin M₂ → Fin A.size`. For each pool independently assume it represents every actual closure node: every `z∈Z` is a prefix of some `A.kptOriginal(originalᵢ v)`. No equality of the chosen names, duplicate-freeness, minimal pool, or equality of their cardinalities is necessary.

Track C's *verified* `finiteNumericH_named_pool_cut_crossing_and_upper_types` gives Cover and Graph separately for each pool's actual `closureSelectedBoringData`. Apply the preceding source-graph uniqueness lemma: these two complete physical one-cut crossing functions agree on exactly their source domains, with identical fully assigned upper L+ types. Thus the intrinsic **physical crossing** is canonical for the closure at a no-(I2) cut, even though its finite original-name representation is not.

The same argument applies pointwise along any finite list/set of cuts if each compared pool represents the **same actual Z(c)** at each cut and the no-(I2) premise holds at each cut. This is pool-independence, **not** occurrence-independence.

## Hostile checks

1. **No two-sided Cover:** `F` may omit a genuine crossing, while `G` includes it. Both could satisfy Graph alone; the source sets need not agree.
2. **No two-sided Graph:** `F` may add an arbitrary source not realized in `Z`. It may still cover every genuine crossing but has extraneous source data; domains differ.
3. **Different closures:** even with the same ambient `A`, replacing `Z` by `Z' ` can add or delete crossing types; a shared source map must not be claimed. Fixing Z *literally* is essential.
4. **An (I2) meet:** two nodes `z,w∈Z` may have equal old ancestor at `c` and distinct next ancestors. There is then no single function `F.target T` simultaneously covering both; Track C's no-meet input is not cosmetic.
5. **Auxiliary E:** two crossing outputs with the same ordinary L reduct but different E are **not** the same full prescribed upper type. Source-graph equality compares complete `PartialTypeWithE`.
6. **Empty closure/source:** both sources may be empty, in which case the conclusion is valid but vacuous. It does not establish geometric existence of a nonempty crossing.
7. **Fake numerical positions:** odd fake coordinates can contribute incoming E bits of physical originals; they may not be treated as independently selected real original-name targets. The theorem preserves their E bits by transporting the *whole* type.
8. **Global upper bound remains open:** nothing here proves that closures of *different occurrences* have a common source in the same Kpt coordinates, that all (I2) cuts can be classified, or that all I1/I2/I3/B3 microevents agree. The manuscript's `Kk_Diary_Determines_Envelope` and `Kk_Diary_Finite_Carrier` remain PENDING.

## Integration contract to Track E

The stagewise comparison no longer needs to identify which pool representative was chosen at non-(I2) cuts, provided it can identify **the same complete closure** and match the cuts in common source coordinates. All physical upper-type assignments then follow automatically from Cover + Graph. This removes one auxiliary choice problem from Track E, without inventing the still-missing cross-occurrence closure identification.
