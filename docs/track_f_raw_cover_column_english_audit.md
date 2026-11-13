# Track F: abstract-to-concrete age-cover bridge over genuinely raw word bounds

**English proof and adversarial audit before Lean.** This fills a missing scope distinction in the manuscript's proof of `Lem:Concrete_Abstract_Correspondence`: the word-level bound `phi` is generally **not itself a graph age**, only `G_phi=F`. The previously merged `diaryCoverColumnCanonical_exact` starts from the canonical age `F`; a separate theorem is necessary to apply the restriction directly to `phi`.

## Lemma A: canonicalization commutes with adding the same raw column cap

Let `B,C` be arbitrary raw integer clique-capacity bounds on nonempty admissible support sets, and suppose their canonical maxima coincide, `G_B=G_C`. Fix **any** set of active sorts `X`, possibly of size bigger than `ell-1`, and any natural cap `n`. Write `B[X,n]` for the raw bound `min(B(U),n)` on **all admissible nonempty** `U subseteq X`, and `B(U)` elsewhere (analogously for C).

**Claim.** `G_(B[X,n]) = G_(C[X,n])`; indeed the transformed raw bounds admit precisely the same normalized labelled clique vectors.

**Proof.** A normalized vector `w` respects `B[X,n]` if and only if:
(i) it respects all raw bounds B, **and**
(ii) for every nonempty admissible `U subseteq X`, its U-total is at most n.
The equivalence follows from the elementary `x<=min(b,n) iff x<=b and x<=n` on affected supports. By the already verified canonicalization-preserves-clique-vectors theorem, `G_B=G_C` implies a vector respects B iff it respects C. Condition (ii) is identical for B and C. Hence the two transformed feasible-vector sets coincide. The genuine finite canonicalizer is the supportwise supremum over exactly these feasible vectors, so their canonical graph-age values coincide at every support.

No age hypothesis is required for B or C: the finite supremum is defined even for raw bounds below a true graph age. In particular a zero raw cap causes no logical problem in this auxiliary lemma, though resulting values may leave the manuscript's positive-age domain.

## Lemma B: the literal raw-word age-change column realizes the intended cover

Suppose `lower ⋖ upper` is a genuine cover in the finite normalized K_ell integer-witness age poset and `T` is a changed admissible support: `lower(T)<upper(T)`. Let `phi` be **any raw word bound with** `G_phi=upper`. Append the concrete age-change symbol `n=ell-1-lower(T)` to precisely the branches in T and 0 to all others. The resulting raw bound is `phi[T,lower(T)]` (this last equality is the **literal word-column formula**, which must be separately checked for the actual concrete-word definitions).

Then `G_(phi[T,lower(T)])=lower`.

**Proof.** Apply Lemma A to `B=phi`, `C=upper`, `X=T`, `n=lower(T)`. This identifies `G_(phi[T,n])` with `G_(upper[T,n])`. The latter equals `lower` by the merged `diaryCoverColumnCanonical_exact`, whose hypotheses are exactly the true cover and changed support.

This shows the selected-front **full normalized clique profile** is reconstructed by the raw word column, without silently replacing `phi` by `G_phi`. It is independent of witness splitting, controlled coding and any numerical-H (B3) properties.

## Hostile scope checks

1. **Raw slack matters:** `phi` may be strictly above its canonicalization at several supports; the previous age-only theorem did not prove this bridge. Lemma A explicitly uses equality of all normalized **feasible vectors**, which is stronger than merely comparing numerical values in an arbitrary noncanonical representation but is implied by `G_phi=upper` in the actual integer-witness model.
2. **Do not replace cover by strict inequality:** Lemma B uses the already verified immediate-predecessor theorem. With an intermediate graph age, capping phi may return the intermediate age, not the proposed lower one.
3. **No need to assume minimal T** for the canonicalization identity: *any* changed admissible T yields the correct cover. Uniqueness of the inclusion-minimal changed support is a separate required fact for reconstructing the *specific diary event* from an abstract cover.
4. **All affected supports:** The column inserts a common nonzero symbol on T, so all nonempty U⊆T acquire a cap, not just U=T. Capping only T in the **raw** word record is not the literal word transformation.
5. **Nonempty support domain:** `U=empty` is not a graph-age coordinate. The condition over U⊆T is restricted to the actual domain.
6. **If X is too large:** Lemma A still applies, since it quantifies over every admissible nonempty U⊆X; it never presumes X itself belongs to the support domain.
7. **Literal word-realization bridge:** The theorem does *not* by itself prove that the new word column alters raw phi by the declared cap formula, nor that the positive symbol `ell-1-lower(T)` is legal and unique for a genuine cover. The concrete raw formula follows by analysis of common symbols; the one-step drop and minimal T remain independent cover-classification obligations.
8. **No lower-bound inference:** This is a local finite dictionary theorem. It does not prove the general decorated inverse or unavoidability.

## Intended Lean formalization

`Kk/TrackFRawCoverColumn.lean`, importing the merged `Kk.DiaryCoverColumn` and new `Kk.TrackFCodingColumn`:
- `trackFCodingRaw_witness_iff`
- `trackFCanonical_eq_of_feasible_iff`
- `trackFCanonical_add_cap_congr`
- `trackFRawCoverColumn_exact`
- `trackFRawCoverColumn_feasible_iff_lower`

Use only `propext`, `Classical.choice`, `Quot.sound`; add an exact-head targeted build/axiom gate and keep the global diary-bijection marker pending.
