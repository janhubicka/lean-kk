# English proof and hostile audit: actual canonical cover-event locality

**4 November 2026. Protocol:** Commit this complete mathematical proof and adversarial review BEFORE writing the Lean theorem. The scope is the *real finite integer-witness graph-age cover event* already defined in the library, not an unconstrained age shadow and not the full numerical-H parameter-closed B3 run.

## Event-local theorem

Let `lower ⋖ upper` be a genuine cover in the verified finite `IsIntegerGraphAge d ell` class, with distinguished changed support T satisfying

  `upper(T)=lower(T)+1`, `ell=lower(T)+r+1`.

(The second equation is the exact canonical clique-block length relation, not an arbitrary cover hypothesis.) The canonical raw block after its final r-th vertex is

  `B_r(U)= upper(U)` for `U≠T`;
  `B_r(T)=min(upper(T),ell-1-r)=lower(T)`.

The previously verified `integerGraphAge_canonical_cover_block` theorem proves the actual canonical result `G_(B_r)=lower`, rather than assuming that raw clipping is a graph age.

For any other nonempty support S of size at most ell-1, suppose every actual nonempty sub-support U of the overlap S∩T satisfies

  `upper(U) ≤ lower(T)`.

Then **the canonical cover step does not alter S**:

  `lower(S)=upper(S)`.

In particular, if S and T are DISJOINT, the overlap premise is vacuous and equality holds. Therefore, for a finite selected subfront E disjoint from the distinguished cover support T, the entire restricted age function on EVERY nonempty support S⊆E remains literally unchanged by this cover.

## English proof

Define `B:=integerAgeLowerAt d ell upper T (lower T)`. The raw bound `B` agrees pointwise with the raw r-th clique-block bound: away from T both are upper; at T, since `ell=lower T+r+1`, `ell-1-r=lower T`. Thus `min(upper T, ell-1-r)=min(upper T,lower T)`.

By the kernel-checked genuine cover-block theorem at stage `a=r`, the canonical age of B is **exactly** lower: `G_B=lower`. Separately, by `integerGraphAgeCanonical_single_bound_locality` (an actual integer-witness proof which zeroes weights outside S), the overlap condition ensures `G_B(S)=upper(S)`. Combining yields `lower(S)=upper(S)`.

If E is disjoint from T, any S⊆E is disjoint from T. Hence no nonempty U⊆S∩T exists, so the overlap condition is automatic. Repeat the equality for every support S within E.

This is an **actual cover macro-event** result. The proof does not identify the gadget's numerical-H original indices, assign any dependent Kpt successor parameters, or prove the full corrected B3 envelope.

## Adversarial audit

1. **Do not assume the raw clipping is already admissible.** Its canonicalization G_B can propagate constraints to overlapping supports. The proof explicitly uses the genuine integer-witness canonicalization and the cover theorem at stage r.
2. **A disjoint subfront is safe, an overlapping subfront need not be.** A selected subfront containing the cover support T must see the drop in age T. Thus the result cannot be promoted to 'every restricted subfront sees equality'.
3. **The stronger overlap hypothesis is numerical and necessary for THIS inference.** For an overlapping S with an old smaller-overlap age above lower(T), canonicalization may cause a secondary change; the lemma imposes the verified sufficient condition and makes no converse claim.
4. **Cover length is exact.** If `r` is not related by `ell=lower(T)+r+1`, the last raw bound need not equal lower(T), so one cannot simply identify the two canonicalizers.
5. **A genuinely admissible cover is essential.** The last-stage equality `G_(B_r)=lower` uses the `AgeCover` no-intermediate property. A general monotone pair of age records is not enough.
6. **The support family consists of nonempty Finset(Fin d) of size≤ell-1.** Empty intersections have no such support U; the overlap condition is vacuous and a disjoint selected subfront is safe.
7. **This does not yet prove the manuscript's all-subfront cover-or-equality claim.** This theorem proves equality on DISJOINT fronts and on specified overlapping supports. A full arbitrary-subfront cover/equality result requires a separate lifting argument for every possible intermediate restricted age.
8. **Real geometry vs age algebra.** Even perfect selected-front age locality does not guarantee the numerical-H gadget is realizable with its required original edges, full auxiliary parameter types, or corrected (B3). The K4 cut-10/cut-22 obstruction remains.
9. **No support E-clique pattern is inferred from raw equalities.** The integer-witness records are age bounds on selected future sorts, not literal original Boolean E adjacency tables. Avoid inferring exact old-neighbourhood certificates from this theorem.
10. **No lower-bound result.** The lemma helps the cover-macrostep part of the upper-bound schedule only; it does not formalize the published one-diary lower-bound theorem.

## Formalization contract

Use genuine `Kk.AgeCover (IsIntegerGraphAge d ell)`, `integerGraphAge_canonical_cover_block`, `integerGraphAgeCanonical_single_bound_locality`, and its `_disjoint` corollary. Prove that the final raw clique bound equals `integerAgeLowerAt`, followed by the exact overlapping-support and disjoint-subfront results. Register named axiom endpoints. English proof first; Lean code after. Run the full pinned Lean build and exact standard-only transitive-axiom report before green manuscript markers; edit OLIVE source prose only and put TODOs on unproved black claims.


## Strengthening (proved in English and adversarially checked BEFORE Lean): inclusion-minimal cover support

The manuscript uses a *distinguished* canonical cover support T. In actual graph-age cover analysis it is important to pick T **inclusion-minimal among changed supports**:

  `hMinimal: for every nonempty U⊊T, lower(U)=upper(U)`.

This is a substantive explicit hypothesis, not inferred merely from the displayed one-coordinate unit drop. The library already proves that any TWO inclusion-minimal changed supports in a genuine cover must coincide (`integerGraphAgeCover_minimal_changed_unique`), but it does not silently choose a minimal one or establish the unit drop for such a choice.

**Stronger locality theorem.** Under `hMinimal`, if S does NOT contain all of T (`¬T⊆S`), then `lower(S)=upper(S)`. Thus **every selected subfront E omitting at least one sort of T** has the same complete restricted graph-age record before and after the cover. Unlike the earlier disjoint-front corollary, E may overlap T substantially.

**English proof.** Fix any nonempty U⊆S∩T. If U=T, then T⊆S, contradicting the assumption. Hence U⊊T and hMinimal gives `upper(U)=lower(U)`. Monotonicity of the genuine *lower* integer-witness age gives `lower(U)≤lower(T)`. Thus every overlap support meets the earlier proved locality hypothesis `upper(U)≤lower(T)`, so `lower(S)=upper(S)`. If S⊆E and T⊄E, certainly T⊄S, proving the whole-subfront result.

**Hostile checks:** (a) If T⊆S, its age can change, so the proof is *not* valid there. (b) Without hMinimal an overlapping proper sub-support U can also be changed; the overlap inequality cannot be manufactured from raw-bound arithmetic alone. (c) The lower age's MONOTONICITY (itself verified from actual integer witnesses) is essential; pointwise lower≤upper is not enough. (d) The lemma does NOT prove the arbitrary-subfront cover-or-equality claim for a front containing T: other supersets of T may be constrained through canonicalization. (e) This result only treats selected graph-age macro-supports; it does not identify numerical-H actual parameter edges, its full corrected B3 future types or one common labelled inverse-source orbit.

**Lean contract:** Add separate named theorems for (1) noncontainment `¬T⊆S` under hMinimal and (2) all eligible supports in a selected subfront E with `¬T⊆E`. Use the already verified `integerGraphAge_monotone` from real integer-witness ages, not an assumed order property. These endpoints must pass full CI and the strict standard-only axiom audit before green manuscript markers.
