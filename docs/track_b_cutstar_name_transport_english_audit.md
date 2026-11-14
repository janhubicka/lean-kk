# KK-free Track B — physical name matching of cross-occurrence cut-stars
**14 November 2026. English-first proof and adversarial audit; stacked on the separately gated cross-ambient Track B PR #129.**

## Why this is a substantive next step

The new cross-ambient theorem `HensonCutOccurrence.full_B3_crossAmbient_iff_of_cutStar_profiles` requires equality of the **sets of permitted complete upper ordinary-L reducts** of two genuine unanchored cut-stars in different physical numerical-Henson structures. This is mathematically sufficient, but an actual resolved-copy construction supplies *original names and physical columns*, not precomputed abstract predicates of type `RelationalPrefixType(c+1)→Prop`.

The following proof converts the abstract type-spectrum hypothesis to a direct physical, name-based relation: for every genuine cut-star original on either side, find one cut-star original on the other side with the SAME COMPLETE directed next-level ordinary-L reduct. This is a usable local audit target for two concrete copies; no equality of the original-name sets or of their full dependent auxiliary E records is claimed.

It also proves that a disagreement in full corrected-(B3) has a **physical name that cannot be matched** to any cut-star name of the passing occurrence. This is stronger than a merely missing abstract permitted upper type.

## Lemma 1 — each actual cut-star name contributes its own exact complete upper-L reduct

Fix one `P : HensonCutOccurrence ell cut hell`, with genuine selected original map `P.original` and full Kpt closure `P.Z`. Its cut-star selection `P.starNames v` implies `P.Full v` and positive physical L-adjacency. By `P.hRepresented`, there is an actual Kpt node `z∈P.Z`, strictly above cut, which is a prefix of the actual ambient Kpt original `P.original v`. The checked theorem `kptBelowOriginal_level_le_free` gives
```
cut+1 ≤ P.ambient.freeLevel (P.original v).val.
```

Thus the true old source type `T=P.ambient.partialTypeAt cut (P.original v).val` belongs to `P.starProfile.source`.

Now the selected-stage prescribed map may choose ANOTHER original name `u` representing the same old type. The checked `selectedStagePoolPrescribedData_source_original` supplies such a chosen name u and the equation
`P.starProfile.target T=P.ambient.partialTypeAt (cut+1) (P.original u).val`.
Both u and v are genuine star-represented closure names. Since their complete old L+ types agree and `P.hNoI2` forbids a competing meet at cut, Track D's verified `kpt_marked_next_full_type_eq_of_no_meet` forces equality of their entire chosen next L+ records. Taking ordinary L reducts yields:

```
P.starProfile.PrescribedUpperLType
  ((P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct).
```

**Key distinction:** this conclusion is NOT automatic for arbitrary selected-stage pools with duplicate old types. It genuinely uses the no-(I2) closure and full name representation. The exact source target may be chosen from a different name.

## Lemma 2 — matching real names forces inclusion of full cut-star upper-L predicates

Let P,Q be two unrelated `HensonCutOccurrence ell cut hell` models, at the SAME source cut. Suppose
```
∀ v, P.starNames v →
  ∃ w, Q.starNames w ∧
    (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct =
    (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct.
```

To show `P.starProfile.PrescribedUpperLType R → Q.starProfile.PrescribedUpperLType R`, unpack a source `S∈P.starProfile.source` witnessing R. The exact chosen-source original theorem gives a name v∈P.starNames with R equal to its real complete next-level ordinary-L type. The matching hypothesis supplies w∈Q.starNames with the same type; Lemma 1 says the type of w is **actually permitted by Q.starProfile**, regardless of how its source target was chosen. Therefore R belongs to Q's permitted complete upper-L spectrum.

No comparison of P/Q lower old socles is needed **for this inclusion**; only the matching of physical upper L-column types. There is no assumption that `P.original v` and `Q.original w` are the same physical index or preserve E.

## Theorem 3 — matching physical cut-star names in both directions gives full B3 equivalence

Assume both directed name-cover hypotheses (P→Q and Q→P) from Lemma 2 and the common old ordinary-L socle condition `SameInitialL P.ambient.L Q.ambient.L cut`. Lemma 2 gives equality of the complete permitted upper-L predicates; the previous PR #129 cross-ambient theorem gives:

```
P.fullProfile.CorrectedB3 family ↔ Q.fullProfile.CorrectedB3 family.
```

This is a direct physical, name-level sufficient condition, strictly weaker than literal equality of the entire dependent L+ crossing relation of Track E. The matched cut-star names may be extra auxiliary originals and are not assumed to be active selected-front diary branches.

## Theorem 4 — a B3 disagreement yields a physically UNMATCHABLE cut neighbour

Assume the two genuine Henson occurrences share their old ordinary-L socles, and P's FULL B3 test fails while Q's FULL B3 test passes. PR #129 proves a real P cut-star original v is eligible and its complete next L-reduct is not in Q's star upper-type spectrum.

By Lemma 1, every genuine Q.starNames name w contributes its real next-level complete L-reduct to that spectrum. Thus no such w can have the same complete next-level L reduct as the failing P original v:
```
∃ v : Fin P.M, P.starNames v ∧
  ∀ w : Fin Q.M, Q.starNames w →
    (P.ambient.partialTypeAt (cut+1) (P.original v).val).lReduct ≠
    (Q.ambient.partialTypeAt (cut+1) (Q.original w).val).lReduct.
```

The missing data have therefore been localized to a genuine, physical, L-adjacent, full closure-selected original name in the failing occurrence. It is not a freely chosen B3-witness future-to-future edge or fake E-positive parameter.

## Hostile checklist

1. Every star name represents a genuine closure-crossing Kpt node; a mere positive L edge or finite address alone does not yield the eligibility bound.
2. The exact equality in Lemma 1 is a COMPLETE next L+ equality, derived from no-(I2) at the SAME closure cut, not merely equality of old ordinary L-socles.
3. Deduplication of old source types may change the chosen representative. The proof explicitly recovers the chosen source name u before applying fibre coherence.
4. A full cut-star name might not be selected by the paper's macrodiary and may be an auxiliary parameter original. No projection to selected F is claimed.
5. Matching names is **relational**, not injective, not necessarily surjective, and does not require equal name-set cardinalities.
6. Both ambient structures may have different E values; only the complete ordinary-L next reducts of matched names are compared.
7. All directed L atoms, absence bits, singleton data and the cut-edge are included. A mere support subset or adjacency of the cut is insufficient.
8. Future–future edges in an arbitrary corrected B3 continuation W remain freely chosen. No ambient upper–upper edges are transported.
9. Two-way name coverage and common old L-socle are sufficient for B3 equivalence; they are NOT an automatically verified canonical resolved diary invariant.
10. The source cut must have the same integer coordinate on both occurrences, or a prior source reindexing must supply a type-correct transport.
11. Empty cut-star: both directed name-coverage conditions hold vacuously for two empty stars, and the upper spectra are both empty; no invented anchor is introduced.
12. If only one direction of physical name coverage holds, only the corresponding B3 implication follows; do not claim an equivalence.
13. The missing witness of Theorem 4 lies in the FAILING occurrence, not necessarily both occurrences. Reversing failure/pass would change direction.
14. Full source records and common labelled inverse-source monoid orbit require much more than this local B3 comparison. Track E's event-indexed data remain necessary.
15. No physical old-prefix REALISABILITY or relative-profile/B3-loss bridge is inferred from this cross-ambient criterion.
16. No unconditional KK-free exact big Ramsey formula or global circulation validation marker is warranted.

## Verification discipline

This note precedes the Lean module `Kk/B3CutStarNameTransport.lean`. Plan four named standard-only axiom reports (physical star name upper-type membership, one-sided name matching → spectrum inclusion, two-way matching → full B3 equivalence, and failing B3 → unmatched physical star name), full `lake build` and strict parser self-test. The first cross-ambient PR #129 must be independently exact-head verified/merged before this stack is merged. If its expected 540-report gate passes, this stack targets **544** reports. No black manuscript changes.
