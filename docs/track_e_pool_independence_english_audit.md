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

## Corollary: corrected (B3) is independent of the representing pool

The corrected (B3) finite age-test of a prescribed B1/B2 function `F` is quantified over every old source `T ∈ F.source` and all L-only continuation structures whose ordinary socle agrees with `prescribedOrdinarySocle (F.target T)`, with each upper ordinary-L type in the image predicate `F.PrescribedUpperLType`.

If two functions have the SAME source predicate and the SAME complete upper L+ target on that source (as above), the corresponding L-only allowed-upper-type predicates are equal pointwise: for each witness type `R`, the same source `T` serves as a witness on both sides. The ordinary socles are also literally equal because the full targets are. Thus `F.CorrectedB3 family ↔ G.CorrectedB3 family`, with no E assignments to arbitrary age-test witness structures. This yields a **physical finite numerical-H no-(I2) theorem**: changing between any two complete finite original-name pools representing the same actual closure preserves corrected (B3).

**Adversarial limits:** equality merely of selected old source sets is not enough—different chosen next outputs can change allowed future types; equal upper ordinary-L predicates with unmatched old socles need not suffice; different actual closures or any unrepresented crossings are excluded. The corollary says only `(B3)` cannot depend on the *choice of the complete representing pool for a fixed closure*. It does not imply that all nonstructural levels are boring, that any one particular (B3) verdict holds, or that two different diary occurrences have matching closures.

## Structural strengthening: the canonical complete crossing RELATION (works even at I2)

The prescribed `F.target` is total only for coding convenience; its values outside `F.source` are arbitrary and must *never* be compared. Instead define the **actual complete crossing relation** for a genuine closure `Z` at cut `c`:

`Cross_Z(c,T,U)` iff there exists `z∈Z` of level `>c` with complete raw old ancestor `(c,T)` and complete raw next ancestor `(c+1,U)`. The records `T,U` are full `PartialTypeWithE`, preserving every negative L and auxiliary E bit. This relation is canonical **regardless** of the representing original pool, and it exists even if two old source types have incompatible upper branches (an actual I2 obstruction).

**Theorem (non-functionality detects I2).** If `Cross_Z(c,T,U)` and `Cross_Z(c,T,V)` hold for `U≠V`, then there exist `a,b∈Z` in the same tree component such that `lev(meet(a,b))=c`. Proof: take the actual witness nodes `a,b`. Equality of their old complete ancestor `(c,T)` makes them share a common ancestor and hence a component. Inequality of upper types makes their ancestors at `c+1` different. If their meet did *not* lie at `c`, the verified successor-tree `nextPrefix_eq_of_no_meet` would force these ancestors equal—a contradiction. Thus a genuine competing meet occurs exactly at `c`.

Consequently failure of I2 at a cut makes `Cross_Z(c,-,-)` single-valued. This statement is about the **actual** parameter-closed closure `Z`, with no selected-shadow projection. The converse (any meet at `c` forces multivalued crossing) is **not** asserted: a meet at `c` may involve a source node ending exactly at the cut and hence not give two crossing upper witnesses.

**Theorem (prescribed graph equals physical relation).** If a prescribed `F` has both `CoversClosureCrossing` and `IsCrossingGraphOf` for the same real `Z`, then `{(T,U) | T∈F.source ∧ F.target T=U}` equals exactly `Cross_Z`. The forward implication uses a genuine graph witness of each prescribed pair; the reverse implication uses coverage of the genuine crossing witness. No choice is involved. Track C supplies both facts for each physical finite numerical-H source pool at every no-I2 cut.

**Adversarial negative:** at an I2 cut `Cross_Z` may be genuinely multivalued. A *total* prescribed B1/B2 function cannot represent all crossings there; one must record the I2 structural event, not force an arbitrary choice of upper output. Moreover equality of relations for **two distinct closures** still requires geometric synchronization; canonicality within one closure alone does not prove the paper's common inverse-source orbit.
