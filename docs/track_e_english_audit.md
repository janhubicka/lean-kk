# KK Track E — full labelled source comparison (English proof and adversarial audit)

**Checkpoint:** 13 November 2026. **Branch:** `kk-track-e-labelled-orbit-20261113`. **Status:** conditional comparison criterion only; the numerical-`H^+` hypotheses from Tracks B–D are NOT discharged.

## Exact statement to prove

Fix a finite ordered label set `Fin n`, a common **named parameter-node domain** `P`, and a common domain of interesting/microdiary-event positions `J`. An *entire pulled-back source record* consists of:

1. the actual labelled selected `G^+` source vertices `s : Fin n → G^+`;
2. a source node for **every** named auxiliary/closure parameter `p : P`, represented as a genuine admissible `Kpt` node;
3. assigned ordinary/old and upper `L^+` types on **every** selected or parameter position (`Fin n ⊕ P`);
4. its complete event kind at each `j : J`, including nonstructural `(B3)` microevents.

This is a common-index *record*, not an unlabelled isomorphism class or a selected-`F` shadow.

For two occurrences, let `F,G` be their **genuine monoid maps** and let `R,S` be their respective full pulled-back records. Suppose:

* each labelled selected source maps to its stipulated target, and both target tuples are strict prefix chains in the same label order;
* the full inverse images, under the induced `G^+` actions, of the two **selected target vertex sets** coincide as literal subsets of the fixed source presentation;
* each parameter source maps to its stipulated target `Kpt` node, the singleton inverse-image sets for corresponding named target parameters coincide, and the second map is injective on these parameter fibres (global injectivity suffices);
* the old-type, upper-`L^+)-type and event functions on the complete common source record agree pointwise.

**Conclusion.** `R = S` as full labelled source records. In particular, there is a **single** injectively labelled source tuple mapping to the two target tuples by `F` and `G`, respectively. This is a common **outgoing** monoid orbit from the source, not a symmetric group orbit or an isomorphism of abstract minimal envelopes.

## English proof

The existing theorem `Kk.labelled_prefix_sources_eq_of_inverse_image_sets` applies to the strict target prefix chains. By injectivity of the genuine induced `G^+` action, the inverse image of a finite selected target set is *exactly* the finite set of prescribed selected source vertices; equality of these two inverse sets gives equality of source-vertex sets. Reflection of proper-prefix order gives increasing source-code lengths, hence the unique increasing enumeration of that set forces equality **label by label**.

For a fixed named parameter `p`, the first source node lies in the inverse singleton fibre of its target under `F`. Equality of corresponding singleton fibres puts that same source node in the inverse fibre under `G`. Both it and the second occurrence's stipulated parameter source node are sent by `G` to the same target node. Injectivity on the fibre forces equality. Repeat for each named parameter, giving equality of the full parameter assignment.

The other three fields are the explicitly compared **total** type and event functions. Extensionality of a five-field record now proves literal equality `R = S`. The common source tuple is injective because its image under `F` is an injectively labelled target. Coordinatewise genuine induced action maps it to both targets.

For a *family* of occurrences, choose one canonical full source record `R_Θ` for each diary `Θ` and prove that the full pulled-back record of **every** occurrence with that diary equals `R_Θ`. Once the selected tuple of `R_Θ` is a prefix chain with a common cap, the already verified `Kk.prefix_chain_orbits_colour_factors` supplies a **uniform finite type-respecting carrier** for that diary and the upper colouring bound. Its orbit hypothesis follows from the literal record equality and the actual maps. No extra countable source or new Ramsey theorem is needed.

## Hostile audit: assumptions that cannot be dropped

1. **No strict-prefix chain → labels can swap.** Two enumerations `(0,1)` and `(1,0)` have the same unlabelled set but are not the same labelled source. The strict-chain hypothesis is used precisely to recover labels, not to prove full source equality by itself.
2. **Same selected set but different parameter closure.** Keep selected source vertices `(0,1)` unchanged and take a named auxiliary source `p` at source node `2` versus `3`. All selected-set comparisons agree, but full records differ. This refutes upgrading `OrderedSourceIdentification` alone to the diary-envelope lemma.
3. **Same nodes but changed upper `L^+` assignment.** Fix selected vertices and parameter-node assignments and change a single auxiliary `E`/upper-type value. Ordinary-`L` selected comparisons (even complete selected ordinary ages) do not see it. A separate full upper-type comparison is mandatory.
4. **Invisible nonstructural events.** An auxiliary `(B3)` loss may occur while the selected `F` age is unchanged; the actual K4 cuts 10 and 22 are regression obligations from Track D. An event-comparison hypothesis cannot be replaced with “all nonstructural cuts are boring”.
5. **Range is essential.** An empty inverse singleton fibre does not identify any source. The statement retains actual chosen source nodes with target image identities, not merely equality of two possibly empty inverse fibres.
6. **Named domains must be complete and aligned.** Comparing a partial list of parameters is insufficient: `P` must contain every node inspected in `I1/I2/I3/B3`, fake numerical sources, old/upper columns, the auxiliary `E` column and free-cut/H/Kpt maps. Relabeling the parameters by an abstract isomorphism is not literal equality.
7. **Monoid direction matters.** An arbitrarily chosen long-gapped occurrence need not map to a shorter-gapped occurrence. The source for `Θ` must be a common compressed inverse source; a pairwise abstract isomorphism of envelopes does not produce the maps required by the theorem.
8. **Theorem quantifiers matter.** Pairwise equality against unrelated chosen source presentations is weaker than `∃ R_Θ ∀ e`; all comparisons must use the *same fixed source coordinates*, with the same event and parameter index sets.

## Still-open geometric contracts

* **B (and A):** construct actual numerical `H^+` resolved occurrences and genuine endpoint-covering envelope maps; provide images for all selected vertices and parameters.
* **C:** construct a **total**, exact, parameter-closed source record in those coordinates, including all ordinary and upper `L^+` assignments, free cuts, fake sources and auxiliary `E` columns. Prove named inverse singleton-fibre comparisons, not simply an unlabelled closure isomorphism.
* **D:** prove exact correspondence of `I1/I2/I3` and full corrected `B3` event labels across occurrences; classify extra microdiary labels when needed.
* **E after B–D:** establish the inverse-selected-set and parameter-fibre equalities **uniformly across every pair of occurrences of a diary**; extract one canonical record and genuine outgoing maps; apply the conditional finite-carrier/Ramsey transfer.

**Validation policy:** no global green mark and no unconditional upper bound is justified by the conditional abstract record theorem. The source-exact Lean build and named standard-only axiom checks are additional requirements before accepting the module.
