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

## Pairwise-to-uniform quantifier bridge (formalized)

A chosen occurrence `r(i)` of each realized diary `i` is **not** itself generally a universal monoid source. Use instead the full pulled-back record `R_i = pulledBack(r(i))`. If `pulledBack(e) = pulledBack(e')` holds for **every pair** of selected occurrences of the same diary, then `pulledBack(e)=R_{diary(e)}` for every selected `e`. Assume the representatives' selected source codes form actual finite prefix chains with named top codes and the genuine maps carry the preimages to every target. Then `prefix_chain_orbits_colour_factors` supplies one intrinsic finite carrier per diary and the claimed upper colour factorization. This argument requires **both** that each realized diary has a chosen occurrence and that pairwise equality is literal in one fixed source coordinate system. The choice of a representative must not be confused with an arbitrary uncompressed source orbit.

Lean: `Kk.pairwise_full_source_comparison_implies_diary_colour_bound`. It is a conditional quantifier conversion, **not** proof of the still-missing per-diary source equality from the macrodiary.


## E2 adversarial correction: a flat type field is not a full Algorithm-5.4 trace

The first Lean record `FullLabelledSourceRecord` deliberately abstracts the type payload as arbitrary `Old, Upper`. This is a **conditional snapshot interface**, not proof that one type per named node exhausts the actual parameter-closed source. Actual `I1/I2/I3/B3` tests inspect **different cut levels**, and both an assigned upper type and the active source/parameter pool can change with the cut. Therefore a full instantiation must carry, in the SAME normalized source coordinates:

* a fixed finite *event index set* (including all auxiliary microevents, not merely macro diary events), whose order/compressed cut values are part of the record;
* the exact set of **present named sources at each event**; old and upper `L^+` type assignments at **each** event for every named source (not one global type per source);
* complete event payload: event kind, **ordered participating selected/parameter names**, compressed source cut, and assigned successor-character data. A naked `I1/I2/I3/B3` tag is not enough to compare source incidences;
* explicit actual source values (genuine Kpt nodes for each named parameter, genuine G+ vertices for each selected label), normalized in a *fixed source presentation*.

**Hostile regression 1 (time indexing).** Give one named source, two event levels 0,1, equal labels/parameters/event-kind tags and the same old type at level 0. Change its upper `E` assignment at event 1. A comparison of global type snapshots at event 0 accepts the two records, but the true full traces differ. The per-event upper field detects the difference.

**Hostile regression 2 (incidence).** At the same compressed cut let two `B3` events have the same tag, but one refers to source parameter `p` and the other to `q`; or have identical names in different ordered slots. Event-kind equality alone accepts them. An **ordered source-name list** in each event frame catches the difference.

**Hostile regression 3 (membership).** Keep all named node IDs, types and event tags equal but make one parameter eligible/active at a cut in the first run and absent in the second. Without a per-cut active mask, equality is spuriously asserted.

**Hostile regression 4 (unbounded boring gaps).** Corresponding target event cuts may have different raw numerical values due to inserted boring levels. Equality must compare *compressed source cuts*, not raw target positions. This is not a harmless notation change: a fake parameter level may survive compression and then must be included in the refined event index.

### Strengthened English lemma for Track E

Define a synchronized event-indexed source record `R` whose literal selected tuple, named parameter nodes, active masks, per-event old and upper types, and *full event frames* are all total functions on **fixed, shared index sets**. Suppose two actual envelope maps `F,G` and target ordered strict prefix chains satisfy the selected inverse-set equality, and suppose all named source parameters admit **equal normal-form recipes** from the same aligned seed, positive-original-parameter, and ambient-original assignments. Normal forms are only the three cases from Track C (seed, selected positive parameter, meet of two compatible ambient originals). Suppose the generator assignments are literally equal in the canonical source coordinates, and the two records agree in active masks, per-event assigned old/upper types, and complete event frames. Then the full event-indexed source records are **literally equal** and the same labelled selected source maps to both target copies under the actual monoid maps.

**Proof.** The existing strict-prefix inverse-set lemma identifies the labelled selected tuple. Extensionality for each named seed, positive source parameter and ambient original identifies their values, hence evaluation of the same seed/parameter/meet recipe identifies every named parameter node. Induced-meet evaluation is deterministic; each meet recipe must be certified as arising from a compatible ambient original pair (Track C's normal form supplies such a certificate). The remaining event-indexed fields agree by the stated complete comparisons, so record extensionality gives equality. This proof removes the *unnecessarily strong* singleton-fibre equality assumption from the earlier source-parameter comparison, **when valid common recipes are supplied**, but does not produce the recipes or prove the comparison from the macrodiary.

**Dependencies.** Track C must provide actual physical source atoms and the complete recipe of each named closure node at every cut, with fake source and auxiliary `E` types; Track D must provide the full event lists and corrected B3 comparisons, not merely a selected-stage cut-visible ordinary-`L` equivalence. In particular D's `henson_selectedStageB3_iff_cut_visible_output_equivalence` compares a *Boolean B3 verdict* on one fixed numerical H; it does not itself identify event source names or upper `L^+` assignments across two H presentations. Track B must provide actual normalized envelope maps. This is a **conditional comparison lemma**, not a proof that equal macrodiaries satisfy the hypotheses.

The strengthened `FullEventIndexed... ` Lean API must be tested on the branch with explicit module build and named axiom checks before any new claim of Lean verification.


## E3: recovering assignments from a complete event frame (English-first)

The E2 comparison still explicitly assumes equality of the per-event `oldAt` and `upperAt` functions. A potentially useful *weaker* geometric contract with Track C/D is **two-sided local determinacy**. Let `node_R(x)` return the actual selected G+ code or the named dependent Kpt node for a source name `x`. Suppose there are fixed reconstruction functions, shared by both occurrences,

`old(j, frame, node)` and `upper(j, frame, node)`,

such that at each synchronized event `j`, the actual assigned old/upper `L^+` types in **both** numerical presentations are exactly these functions evaluated on their actual event frame and source node. If the selected/parameter nodes, full frames and per-cut presence masks agree, then every old and upper assignment agrees: substitute equality of the frames and nodes into the two reconstruction formulas. Thus the event-indexed full records agree literally.

**Important hostile test.** Equality of old source types (or just of cut-edge bits) does *not* prove local upper determinacy. The selected-stage prescribed-output construction can choose different representatives of the same old source with different next-cut complete upper L-reducts. D's fibre-coherence audit exhibits exactly this obstacle. A reconstruction function must include the genuinely chosen **successor character/output** as part of the frame, and C/D must verify it computes the **complete L+ assignment**, including auxiliary E, not just the ordinary L reduct. We therefore cannot replace local determinacy by a bare assertion that the macrodiary lists the same event kind.

**Nonunique meets.** Track C's normal form is existential, not a unique canonical decomposition. In a branching rooted tree the same meet may equal meet(a,b) and meet(a,c) for different b,c. Thus choosing the same seed/parameter/meet *recipe* across distinct occurrences requires either a deterministic normalization theorem or a proof that evaluation is independent of choices. The E2 Lean comparison assumes literal agreement of the **chosen** recipes and their underlying physical atoms; it does not derive that agreement from the closure normal form.

**Absent sources and fixed indexing.** Current formal fields are total maps with a separate presence mask. For an eventual physical instantiation, assignments at absent source/cut pairs must have a *shared fixed convention* (for instance `Option` with `none` for absence), not arbitrary witness-dependent values. A finite per-diary parameter/event index or a uniform finite padded index must be justified, including every auxiliary microevent. Raw numerical target cut levels are not the same as compressed source event ranks.

**Target-node transport.** Even literal equality of the source records does not alone prove that a chosen monoid map sends every dependent source parameter to its *actual target Algorithm-5.4 parameter*. This map-compatibility is an independent check for the full minimal-envelope assertion, although the labelled selected-vertex orbit suffices for the already verified conditional Ramsey transfer. Track E should expose this transport as a separate explicit endpoint.


## E4: non-vacuity — complete source coverage, not just equal named records

An indexed "full" record is **not** automatically a complete encoding of the actual Algorithm-5.4 closure. Two occurrences can have literally identical selected and named parameter records if the index set omits a generated meet, even though their actual closures differ. In the extreme, choosing an empty parameter index makes all the parameter comparisons vacuous. Thus an unconditional application of the record comparison requires, for every synchronized scan cut `j`, the explicit **coverage equation**

`z ∈ actualClosure(j) ↔ ∃ p, record.presentAt(j, parameter p)=true ∧ record.parameters(p)=z`.

The right-hand side must include **all** actual seeds, selected positive-free-level parameters, and meets in the full parameter-closed source. Source parameter names may be redundant, but no actual node may be omitted.

**Lemma.** If two actual presentations have complete coverage by the same literal event-indexed record `R=S`, their parameter-closed source sets agree at every synchronized cut. **Proof:** use equality of the record's parameter map and active mask to identify their images pointwise; the two surjective coverage equations then identify each actual closure set by extensionality. This is a property of literal pulled-back source sets; it does *not* claim equality of the corresponding *target* closures without separate monoid transport.

**Adversarial limits.** C's normal-form theorem only establishes that each closure node is *representable* as seed/parameter/meet; it does not provide a fixed finite index or a coherent choice of names/recipes across all occurrences. E must require an actual coverage certificate in addition to agreeing recipe data. Likewise the full event-index itself must cover all I1/I2/I3/B3 microevents in the real run; parameter coverage alone is not full event coverage. These are geometry obligations, never automatic properties of a Lean record structure.
