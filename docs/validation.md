# Verification plan

This project checks the manuscript proof of optimal big Ramsey degrees of
the universal \(K_k\)-free graph. Statements in the present document are
not claims of completed kernel verification unless the corresponding CI
job has passed.

## 22 October — envelope source and ordered-label reduction

The latest complete Lean checkpoints are:

- [Run 39754299181](https://github.com/janhubicka/lean-kk/actions/runs/39754299181),
  commit `0d306b31b18416b45520ea2fd9e7164fee2bccda`:
  `labelled_prefix_preimages_of_range`,
  `labelled_prefix_sources_of_Kpt_envelope`,
  `labelled_envelope_produces_intrinsic_source`.
  A genuine Kpt envelope covering the top and both endpoints of
  each labelled representing pair automatically has a genuine finite
  labelled **prefix-chain preimage**, with an actual intrinsic
  full-profile representation in the fixed G-omega.
- [Run 39754682204](https://github.com/janhubicka/lean-kk/actions/runs/39754682204),
  commit `fcd9b3c240faab3655b6312003cffa8311a2670c`:
  `labelled_prefix_sources_eq_of_unlabelled_range`.
  Increasing finite enumerations of the same set of G+ prefix
  codes agree label by label. Arbitrary incomparable same-size
  G+ vertices are NOT covered by this statement.
- [Run 39755719215](https://github.com/janhubicka/lean-kk/actions/runs/39755719215),
  commit `ca349d8040fa71f808ad0f451e8e648f3f2eadd3`:
  `source_range_eq_inverse_image` and
  `labelled_prefix_sources_eq_of_inverse_image_sets`.
  The latter proves the direct paper-facing implication from
  equality of the **unlabelled selected-vertex inverse-image sets**
  under two genuine G+ actions to equality of their labelled sources.

All listed jobs passed full `lake build` and the named
transitive axiom audit; the endpoints use only
`[propext, Classical.choice, Quot.sound]`. An additional scan
of the 12 Kk source modules found no active `sorry`, `admit`,
`axiom`, or `unsafe` declarations outside comments.

**The unresolved diary-specific theorem** is now exactly the
equality of the marked selected-source inverse-image **sets**
for different occurrences having the same labelled diary. The
generic envelope-choice theorem compares two runs for the same
selected set, not this cross-occurrence relation. Matching the
whole unmarked auxiliary closure is not enough unless one also
recovers its distinguished selected subset. The full
parameter-closed (I1)--(I3) data, especially auxiliary (B3)
age tests, must still be checked.

The paper's `validation.tex` distinguishes these proved
generic implications from the unverified exact upper bound and
published optimality/lower-bound argument.

## Verified on 20 October 2026

The finite simultaneous-refinement theorem
`Kk.finite_family_type_respecting_ramsey` compiled in [GitHub Actions run 39346781161](https://github.com/janhubicka/lean-kk/actions/runs/39346781161), against pinned successor library commit `a74c10761303a18649053f2af3a1a1697f032e13`.
The transitive axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.
This establishes the Ramsey-composition step, **not** the labelled carrier,
occurrence factorisation, or optimality theorem.

## Validated labelled-diary transfer (20 October 2026)

[CI run 39371584207](https://github.com/janhubicka/lean-kk/actions/runs/39371584207)
compiled and checked `Kk.diary_colouring_constant` and
`Kk.diary_colouring_factors`. Their transitive axiom lists are exactly
`[propext, Classical.choice, Quot.sound]`.

These results prove that the colour of the transformed selected embeddings
factors through their labelled successor diaries **provided that**
(a) each selected embedding has a representation by the finite carrier
of its diary, and (b) the representation commutes with the induced action.
Neither hypothesis is concealed as an axiom. Their eventual discharge
requires the geometric diary construction.

## Verified geometric and labelled-action interface

[Full Lean run 39505853734](https://github.com/janhubicka/lean-kk/actions/runs/39505853734)
passed `lake build`, the named theorem checks, and all axiom checks against
the pinned successor library. The transitive axioms for the new named
endpoints are exactly `[propext, Classical.choice, Quot.sound]`.

- `Kk/RepresentedVertices.lean`: actual source type pairs, independence
  of representation and global extension, induced G+ equivariance, and
  exact preservation/reflection of binary and auxiliary E records.
- `Kk/LabelledCopies.lean`: labelled injective genuine G+ copies,
  `map_fromPairs`, and conditional colour factorisation through diaries.
- `Kk/CommonCap.lean`: one finite admissible carrier, one upper type,
  and injective labelled source pairs for any family of G+ codes which
  are prefixes of a common top code.
- `Kk.LabelledGPlusCopy.colour_factors_through_diary_of_orbits`:
  genuine monoid-orbit factorisation implies the type-respecting
  factorisation needed by the Ramsey-transfer theorem.

**These do not yet prove the K_k-specific geometrical orbit hypothesis.**
The chosen bounded resolved copy must be identified with codes in one
numerical H+ prefix chain, and each labelled occurrence of a diary must
be shown to lie in the genuine induced monoid orbit of its chosen source.
The global full-closure (B3) age-test projection in the diary/envelope
comparison remains a separate obligation.

## New verified countable-prefix carrier (21 October 2026)

[Actions run 39560836060](https://github.com/janhubicka/lean-kk/actions/runs/39560836060)
on commit `8bbf370e33956bb4c8b5d926697c51999221bc00` passed
the complete Lean build and the named axiom audit. The theorem
`Kk.countable_labelled_carrier` uses the actual
`CountableEnumeratedPartialStructure.toGPlus` representation.
For any finite injectively labelled list of indices and any common index
bound, it constructs ONE genuine admissible `FiniteTypeBase` and one
labelled family of representing pairs. Both source injectivity and equality
with each original G+ vertex are conclusions, not assumptions.
Its transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.

This discharges the abstract common-prefix requirement **once the selected
vertices have been identified as actual prefix codes of the same source
countable L+ structure**. It does not prove that the specially resolved
Henson copy has this identification, that equal diaries yield the same
parameter-closed envelope type, or that all their labelled occurrences
belong to the common monoid orbit. These remain the geometric next steps.

The manuscript uses `validation.tex` (the same margin-marker style as
`lean-successors`) to identify checked endpoints without colouring the
full upper-bound or optimality assertions green. References are pinned to
passed Lean commits and distinguish incomplete implications from the full
mathematical statements.

## Full atomic and labelled-envelope lifting endpoints (21 October 2026)

[Actions run 39562513338](https://github.com/janhubicka/lean-kk/actions/runs/39562513338)
passed the full Lean build and named `#print axioms` checks for
`f430d708ca35e37fcba051db923b84d5eae4587d` (standard axioms only).

- `Kk.countable_labelled_carrier_full_atoms` strengthens the verified
  carrier to preserve all finite directed binary, unary, diagonal and
  oriented auxiliary-E facts (including the absence of atoms).
  The binary theorem explicitly requires distinct labels.
- `Kk.LabelledGPlusCopy.labelled_copy_lifts_of_envelope` says that if
  an actual normalized Kpt monoid envelope covers both endpoints of
  every prescribed representing pair for a labelled G+ copy, then
  *one and the same monoid map* carries a labelled preimage copy to
  that target. This is an existence theorem, not an assumed
  inverse embedding or an unlabelled orbit shortcut.

**Still open:** identify the selected resolved-Henson vertices with their
source countable prefix codes; show that equal diaries give a common
*labelled source* under genuine monoid envelopes; ensure the full
parameter-closed (B3) age tests are covered. Theorem 5.5's choice
independence is for a fixed selected set and does not supply this
cross-occurrence comparison. Also instantiate the generic normalized
binary family faithfully as the symmetric, irreflexive Henson class.

The manuscript's `validation.tex` markers distinguish these verified
geometric implications from the currently unverified upper bound
and optimality corollary.

## Enumerated G-omega and countable-source orbit transfer (21 October 2026)

[Full Lean run 39641050527](https://github.com/janhubicka/lean-kk/actions/runs/39641050527)
at `80b9336e2e4661b3ff154e12b1cfd8fd9204d8d4` checked the real
`Kk.LabelledGOmegaCopy.map_fromPairs` and the conditional diary
colouring theorem after conjugating the genuine G+ action by the fixed
size-ordered enumeration. It also verified
`Kk.LabelledGOmegaCopy.map_lt_of_prefix_in_fixed_enumeration`,
which preserves numerical order **for strict prefix codes**; no global
monotonicity on arbitrary incomparable G+ vertices is asserted.

[Full Lean run 39686917479](https://github.com/janhubicka/lean-kk/actions/runs/39686917479)
at `b11e748c381dd14e1c3e059731325a46a520a6d9` additionally checked
`Kk.countableSourceCopy_finite_representation` and
`Kk.countable_source_orbits_colour_factors`. These construct one finite
full-profile carrier and its intrinsic approximation for each given
countable labelled source; the only remaining geometric assumption in
the Ramsey transfer is that every selected occurrence of a fixed diary
is an image of that same labelled countable source under a **genuine
Kpt monoid map**.

All named endpoints in those runs report exactly
`[propext, Classical.choice, Quot.sound]` and pass the full build.
The normalized (K_\ell)-free graph encoding and the common labelled
orbit lemma for the resolved copy remain separate applications.
`validation.tex` in the manuscript now links to the verified
G-omega and countable-source interfaces, while leaving the full diary
carrier and final upper bound pending.

## Verified finite Henson graph-language equivalence (22 October 2026)

[Actions run 39690515113](https://github.com/janhubicka/lean-kk/actions/runs/39690515113)
at `92ce50e5b04876c830662da1b6168e988262dd4c` passed the complete
Lean build and the named axiom audit (only
`[propext, Classical.choice, Quot.sound]`).

The new `Kk/HensonEncoding.lean` module defines the genuine normalized
signature `AgeTestModel 1 0 1`, together with exactly four kinds of
`NormalizedForbidden` patterns: the positive-loop singleton, the two
asymmetric ordered pairs, and the complete symmetric
`K_ell` (`ell >= 2`). Their required singleton and irreducibility
hypotheses are kernel-checked.

The theorem `Kk.hensonForbiddenFamily_avoids_iff` proves the exact
bidirectional statement that avoiding these patterns is equivalent to
irreflexivity, symmetry, and the absence of an increasing complete
`K_ell` clique. The latter is ordinary `K_ell`-freeness because
any clique admits an increasing listing. The directional inequalities
are real induced ordered copies; the proof does not assume symmetry in
the generic successor library.

This closes the finite-language/forbidden-age dictionary. The
identification with the actual Henson *Fraisse limit*, the construction
and normalization of a bounded resolved copy, and the common
labelled diary orbit remain separate open mathematical/application
obligations. The manuscript's green marker now points to this exact
equivalence and nowhere claims the full upper bound is verified.

## Exact labelled inverse comparison and finite prefix-chain transfer (22 October 2026)

[Lean CI run 39691376167](https://github.com/janhubicka/lean-kk/actions/runs/39691376167)
on `443775de355f05f475d07f4197fb71b142ed2481` passed
`lake build` and named transitive axiom checks for:

- `Kk.common_source_pairs_of_equal_labelled_preimages`: two genuine
  Kpt envelopes with **equal inverse singleton sets** for every label
  and both endpoints of their representing pairs have one identical
  labelled source pair family.
- `Kk.common_labelled_copy_of_equal_endpoint_preimages`: the pair
  family produces one genuine labelled G+ source copy whose images
  under the two monoid maps are exactly the two specified targets.
  Equal unlabelled envelope embedding types alone do **not** imply
  the singleton equalities, and this stronger geometric hypothesis
  remains to be derived from the resolved diary.

[Lean CI run 39691906543](https://github.com/janhubicka/lean-kk/actions/runs/39691906543)
on `2b0cd69f9452d10d4ca22a85ecbee0c40ac76298`
passed the full build and axiom audit for:

- `Kk.prefixChain_finite_representation`: any finite injective
  labelled family of genuine G+ vertices that are prefixes of
  one top code has one canonical admissible full-profile source.
  The identity type-respecting map represents it literally in the
  fixed G-omega enumeration.
- `Kk.prefix_chain_orbits_colour_factors`: if each diary is
  assigned such a fixed labelled prefix chain and every selected
  occurrence is in its genuine monoid orbit, one shape map makes
  the transformed colouring depend only on the diary.

Each new theorem uses only
`[propext, Classical.choice, Quot.sound]`.

**Sharper remaining proof target:** construct a *compressed finite
labelled prefix source* for each successor diary and prove equality of
the labelled inverse singleton preimages of its two Kpt representing
endpoints for every occurrence, under actual minimal envelope maps.
The necessary auxiliary parameter-closed I1–I3/B3 age tests are
still unverified in this diary-specific application. There is no
need to extend the compressed source to a separate countable model
before applying Ramsey. The manuscript's `validation.tex` markers
now distinguish the checked generic implications from this remaining
geometric premise.

## Imported mathematical theorem

The dependency is pinned to
`janhubicka/lean-successors@a74c10761303a18649053f2af3a1a1697f032e13`
and imports `SuccessorTree.Library.TypeRespecting`.
The theorem
`SuccessorTree.V10.normalizedKpt_typeRespectingRamsey` concerns all
intrinsic finite type-respecting maps on the admissible partial types over
a finite partial structure, including the auxiliary relation E. These are
the objects that must be coloured.

## Validation order

1. **Finite simultaneous refinement**: prove
   `Kk.finite_family_type_respecting_ramsey`, allowing the finite partial
   base to vary with the diary. Use the exact monoid composition identity.
2. **Represented graph vertices**: define the pair representation
   \(v(S^+,T^+)\), its equivalence relation and the induced action
   compatible with Observation 6.45 of the successor draft.
3. **Finite labelled carrier**: for each labelled diary, construct one
   finite partial structure and a labelled copy represented by restrictions
   of one top type as in Definition 6.46.
4. **Equivariance**: check that the finite action commutes with the
   induced action on the auxiliary graph, including both directions of
   every binary relation and non-relations.
5. **Occurrence factorisation**: show that every labelled occurrence of
   that diary in the bounded resolved copy comes from the fixed finite
   carrier. This is not implied by an unlabelled envelope isomorphism.
6. **Upper bound**: pull back an arbitrary colouring, apply the finite
   simultaneous refinement, and push back via the two ordered embeddings.
7. **Exactness**: verify the comparison of concrete, abstract and
   successor diaries; import or independently formalise the lower-bound
   unavoidability theorem of the published paper.

## Adversarial checks

- The chosen top type cannot be assumed to be present in a minimal
  envelope: use the finite ambient cap construction.
- The action on the auxiliary graph is conjugated by the fixed
  enumeration isomorphism; it is not literally the action on the
  unenumerated graph.
- The finite carriers must retain the labelled vertices. The bounds
  count labelled diaries, not merely unlabelled shapes.
- The finite Ramsey theorem alone does not prove the lower bound.
  That direction presently uses published diary unavoidability.

The companion TeX and reviewed mathematical exposition live in
`janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs`.
