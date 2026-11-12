# Verification plan

## 12 November 2026 — concrete maximizers of arbitrary raw integer support bounds

[PR #83](https://github.com/janhubicka/lean-kk/pull/83) passed its hosted [full 9,498-job build and 358 strict standard-only named-axiom reports](https://github.com/janhubicka/lean-kk/actions/runs/43172592541) and merged as `1806041a80ae30ac0dc015b6497894fd1aa94ff9`. [PR #84](https://github.com/janhubicka/lean-kk/pull/84) passed its hosted [9,500-job build and 363 standard-only reports](https://github.com/janhubicka/lean-kk/actions/runs/43174868119), merged as `99d6127155ff408d9a2a6b4aed1b074667c5293d`. Their English-first manuscript revisions remain on manuscript PR #22, whose protected-black `kk.tex` text is byte-identical outside the olive block.

**Current next step, English-first and unmerged:** [Concrete maximizer audit](concrete_canonical_maximizers_english_audit.md) gives an explicit finite complete ordinary-L typed clique attaining the canonical raw integer-age bound G_B(T) for each support T, even when B is not a genuine age. The Feasible(B) set is nonempty for ell>0 by the genuine normalized all-zero vector; finite supremum is attained; the previously checked `IntegerWitnessVertex w` Sigma-type gives the actual labelled clique. All subsets of any feasible component obey the **entire joint** raw support constraint system. Different T may require different maximizing components; none is asserted to extend an arbitrary fixed Henson old prefix.

`Kk/ConcreteCanonicalMaximizers.lean` is a dependent Lean implementation of six named endpoints, currently pending **369 exact named transitive-axiom reports** and a full hosted `lake build`. Do not count this branch as validated until the hosted report passes. The remaining full universal gadget, relative old-neighbourhood completion, auxiliary Kpt E/parameter records, full corrected-B3 and common labelled orbit are open; no new manuscript green marker is authorized on these global obligations.

## 12 November 2026 — English repair of the conditional boring-level criterion

The editable olive `Lem:Kk_Boring_Level` in [manuscript PR #22](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/pull/22) previously inferred physical relative (B3) witnesses merely from changes to an abstract graph-age function. This inference is invalid without a *faithful relative-profile realization theorem* over the complete fixed old L+ source. The repaired English statement/proof and explicit triangle-free relative obstruction are recorded in the [adversarial audit](boring_level_relative_profiles_english_audit.md), committed BEFORE the Lean implementation.

The new `Kk/FaithfulRelativeB3Profile.lean` contains **three** conditional endpoints. For genuine ages F_before,F_after and two relative-continuation predicates, it proves (a) equality of F iff equality of all relative predicates **assuming each is faithful to the full normalized feasible-vector system**; (b) under no creation of relative continuations, age inequality iff some relative vector is *lost*; (c) under a separately supplied full corrected-(B3)-loss equivalence, absence of B3 failure iff the age states coincide. The actual numerical-H/Kpt full-source fidelity, its stagewise monotonicity, B3-loss equivalence, (I1)/(I2) exclusions and common labelled orbit are **not** asserted or verified by these endpoints.

In addition, `Kk/RelativeTriangleObstruction.lean` formalizes the concrete hostile regression: with old vertex 0 adjacent to 1 and 2 in a symmetric graph, also adding edge 1–2 creates an actual 3-clique. Hence under K3-freeness that future edge must be absent. Both statements compiled against the literal existing `IsDirectedCliqueOn` and `HasCliqueBelow` definitions, using only standard axioms. No universal resolved-copy counterexample is claimed.

All three proof bodies were compiled in pinned local Lean 4.35.0-rc3 against the exact finite-integer-age interface, with only `propext`, `Classical.choice` and `Quot.sound`. The formalizations are stacked after the four endpoints in PR #83; **363** exact transitive-axiom reports and a full hosted build are required before merge. No global boringness, resolved-copy or upper-bound manuscript marker is upgraded.

## 12 November 2026 — abstract clique-profile repair and independent relative-realization obstruction

The corresponding editable/olive passage of [KK manuscript PR #22](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/pull/22), Lemma `Lem:Extension_Profile_Determines_Age`, has been repaired **in English before Lean**: a consistency vector witnesses an abstract permitted labelled clique, but its realization as a Henson extension over a fixed old prefix with prescribed old-neighbourhood L atoms requires a separate complete neighbourhood test. A triangle-free obstruction is recorded in the [adversarial audit](extension_profile_vs_relative_realisation_english_audit.md): two new vertices both adjacent to one old vertex cannot also be adjacent to one another, although the abstract 2-clique alone is admissible. The numerical extension-profile identity itself is unchanged.

`Kk/ExtensionProfileAge.lean` now formalizes **four** bounded abstract-age endpoints using the **existing** `IsIntegerGraphAge`, `IntegerCliqueWeights`, `WitnessRespects` and `integerGraphAgeCanonical` definitions. For genuine F, F(T) is the supremum of counts on T over all feasible normalized labelled vectors; for arbitrary B,C, equal full feasible-vector systems imply G_B=G_C; and for genuine F,G equality of full feasible systems is equivalent to F=G. No raw per-coordinate equivalence or relative realization is smuggled in. The four proofs were first checked locally in exact pinned Lean 4.35.0-rc3 against faithful replicas of the imported definitions, using only `propext`, `Classical.choice` and `Quot.sound`. A production full-hosted `lake build` plus the strict expected **358** named reports remains the merge gate; no new manuscript validation mark is authorized before that gate.

The graph-age profile is an **abstract** L-only characterization. Compatible future one-point extensions, full parameter-closed corrected-B3, and the labelled common inverse-source orbit remain outstanding.

## 11 November 2026 — explicit normalized witness components and universal-gadget research

[PR #81](https://github.com/janhubicka/lean-kk/pull/81) passed [hosted run 42995032041](https://github.com/janhubicka/lean-kk/actions/runs/42995032041) (full **9,496-job** build, parser self-test and **345 named standard-only transitive-axiom reports**) and merged as `f3e52841ad886c58860529fa8caf8a0d38a4e06e`. This establishes two-/multi-component finite free amalgamation for already-compatible K_ell-free extensions over one old graph P.

A new [English-first construction and adversarial audit](universal_typed_witness_gadget_english_audit.md) analyzes a finite **universal typed-witness gadget** for any raw integer support bounds B: one reserved clique Q_T of size `ell-1-B(T)` (Nat truncated) for each admissible T; a complete typed clique component C_w for every *feasible* normalized integer vector w; support edges Q_T–C_w exactly according to sort membership in T; and no edges between different support blocks or witness components. The mathematical proof shows the resulting ordinary L graph is K_ell-free, that its future cliques realize **exactly** the feasible normalized vectors, and hence that their maximum support counts equal the actual canonical graph age `G_B`. An independent all-pairs oracle checked **465** bound systems and **377** deliberately inserted infeasible-vector negative controls with zero discrepancies; these are regression tests, not Lean verification of the complete gadget.

First Lean stage: `Kk/IntegerWitnessCompleteComponent.lean` constructs the Sigma-type `Σ j : Fin d, Fin (w_j)` of one vector w, proves its exact total size, exact multiplicity of every sort and every support, symmetric complete irreflexive ordinary L edge relation, absence of an ell-clique when `0<ell`, and preservation of the raw B constraints for any feasible w. The **ell positivity** restriction is essential: `IntegerCliqueWeights 0 0` is inhabited by an empty function because of truncated natural subtraction, but a zero-cardinality component cannot have size below ell=0. This boundary was caught and repaired in the English audit before committed Lean. Nine new theorem endpoints pass independent local pinned Lean 4.35.0-rc3 / Mathlib checks with standard axioms only; the full imported project build and **354 exact named reports** remain an explicit hosted merge gate.

The complete multi-component + reserved-block universal graph gadget is **not** yet formalized in Lean. More importantly, the physically *relative* Henson construction still needs actual old-to-future mixed-neighbourhood certificates, chronological enumeration, simultaneous Q/G/W L-bits, auxiliary E/parameter-closed B3 source matching and common labelled inverse-source orbit. Do not mark the full manuscript argument green on the basis of this abstract L-only gadget.

## 11 November 2026 — free amalgamation of compatible finite L-only witness families

The prior [clique-to-integer witness PR #80](https://github.com/janhubicka/lean-kk/pull/80) passed [exact-head hosted Lean run 42993396533](https://github.com/janhubicka/lean-kk/actions/runs/42993396533) with a **9,495-job build** and **341 exact named standard-only transitive-axiom reports**, and merged as `520acdafdeee105bc613d8c5367e74b32b779798`. Its new `Kk/FiniteCliqueIntegerWitness.lean` constructs normalized integer vectors from all small realized cliques, proves exact values on every support, and transfers the **joint** system of support bounds through the verified canonicalizer. A counterexample prevents wrongly assuming every abstract vector is represented in a fixed future W.

The independent new [English proof and adversarial review](finite_free_amalgamation_witness_families_english_audit.md) and `Kk/FiniteFreeAmalgamationWitnesses.lean` establish the *relative finite free-amalgamation mechanism*: if each P∪W_i is K_ell-free and different fresh pools have zero cross edges, their finite union over the same old base P remains K_ell-free. The two-pool iff also holds without artificial disjointness conditions. Its entire family includes the empty-family case with explicit base-freeness. These core proof bodies compiled locally against the exact directed clique checker and exact Boolean no-clique interface in pinned Lean 4.35.0-rc3 / Mathlib, standard-only axioms; the dependent source requires its own hosted whole-project build and **345 named reports** before merge.

This proves that multiple **already compatible** individual finite L-only witness extensions may be combined with no new forbidden clique. It does not prove that each required relative normalized-vector witness extension exists with all prescribed old-to-future, reserved support, gap zeros, chronological enumeration and auxiliary Kpt E/parameter records. That separate mixed-neighbourhood realization problem is now the main mathematical obstacle. No protected manuscript black prose or green marker was changed.

## 11 November 2026 — exact finite L-clique to normalized integer-age bridge

**Hosted-verified baseline:** the preceding [PR #79](https://github.com/janhubicka/lean-kk/pull/79) passed [run 42909516210](https://github.com/janhubicka/lean-kk/actions/runs/42909516210), including a full **9,494-job** build and **327 exact named transitive-axiom reports** (only `propext`, `Classical.choice`, and `Quot.sound`). It merged as `20ccd8e03b5a232097707662db1fd507aa9b1acf`. This supersedes the historical pending statements in sections below.

**New English-first proof / local Lean checkpoint (unmerged):** the [adversarial audit](finite_clique_to_integer_age_witness_english_audit.md) identifies the exact fibre-counting map from every finite L-clique `s` of size `s.card < ell` to the *existing* normalized `IntegerCliqueWeights d ell` type. The new `Kk/FiniteCliqueIntegerWitness.lean` proves full-fibre cardinality, exact total weight, support-count equality, and the iff between **all** raw support inequalities and the corresponding particular-vector `WitnessRespects` condition. A concrete one-sort, empty-pool counterexample shows that one may **not** infer that every abstract normalized vector is realized by a clique in a fixed W. The **entire joint support system**, not a single support in isolation, is preserved by the existing `integerGraphAgeCanonical_preserves_clique_vectors` theorem.

A separate all-realized-cliques theorem requires W K_ell-free to ensure every clique has total <ell. This condition follows **without a new assumption** from the already required K_ell-free old-plus-future pool P∪W using finite directed-clique capacity monotonicity. The canonicalized raw bound B and the integer graph-age canonicalizer G_B therefore admit precisely the same realized finite-clique vectors on every support of that W, but neither construction creates additional hypothetical W or validates a full B3 source orbit.

**Evidence / gate:** the seven core finite-fiber, witness and generic canonicalizer proofs plus negative realization regression were checked with the exact pinned Lean `4.35.0-rc3` and Mathlib `5bd58ac291422a21f412ae354c91e7d172255a2c`, locally, with only standard named axioms. Fourteen named theorem endpoints have been registered. **A fresh hosted full build and 341-report exact-head axiom gate remain necessary** before merging this branch; no black manuscript prose or green validation marker has been changed.

**Still open:** realize every needed *compatible* continuation vector inside the actual Henson extension with complete old/reserved/gap binary columns; transport it through the integer canonical-age representation; synchronize auxiliary E/parameter-closed corrected B3 source records and the common labelled inverse-source orbit; prove the unconditional Ramsey bounds.

## Physical exact gluing with ALL arbitrary future clique witnesses (10 November 2026)

After the two-endpoint support-witness capacity lemma, `Kk/ArbitraryWitnessGluing.lean` composes the full finite four-pool gluing iff with the exact inequality on the T-part of **every clique** in an arbitrary W. Its generic statement keeps Q∩U=∅, old/reserved nonedges, gap/future zeros, both directed reserve/future L bits, and the past K_ell check. The numerical-H specialization substitutes the verified genuine real-copy prefix capacity `if g<a then a else a+1` (requiring a<r≤k+1 and g≤k). The [English proof and twelve-point hostile audit](arbitrary_witness_gluing_english_audit.md) were committed before Lean. Both dependent endpoints still require the full hosted gate; projected combined count is **327** standard-only named endpoints.

Unlike the selected-top column theorem, these iff statements quantify over arbitrary finite future graph witnesses W under their prescribed columns. They do **not** construct those hypothetical W inside a Henson extension, identify filtered clique cardinalities with normalized integer witness vectors, discharge the old-plus-W forbidden-clique test, or prove parameter-closed B3 source equivalence.

## Arbitrary finite continuation clique witnesses (10 November 2026, English-first branch)

A new independent two-endpoint Lean module, `Kk/FiniteCliqueSupportWitness.lean`, identifies the exact supported-future clique capacity `a+cap(W.filter (sort∈T))<ell` with the corresponding inequality on the T-part of **every** directed clique `s⊆W`. The second endpoint rewrites this under the indispensable `a<ell` condition as the precise natural raw bound `ell-1-a`. The reverse implication uses the **actual maximizing clique subset** from verified `finiteDirectedCliqueCapacity_attained`; it handles empty U and a=0. A pinned local Mathlib Lean 4.35.0-rc3 reconstruction of the full proof with exact existing predicate/capacity definitions compiled with standard-only axioms. The [English-first proof and hostile audit](clique_support_all_witnesses_english_audit.md) precedes the dependent source. Full exact-head hosted build and strict named 325-report audit remain a separate merge gate.

This theorem quantifies over all clique witnesses *in any chosen W*; it neither proves existence of every desired K_ell-free W as a Henson extension nor discharges the independent old-plus-W K_ell test. To identify the result with the **integer** graph-age canonicalizer, one must still convert sort-counts of an arbitrary clique to normalized `IntegerCliqueWeights` vectors and preserve all support inequalities.

## True numerical-H reserved-to-selected top L support (10 November 2026; separate PR)

The next English-first module `Kk/NumericHTopSupportPool.lean` proves injectivity of the actual top numeric position map and exact membership of selected top images; automatic disjointness of a reserved real-copy prefix from all sufficiently later selected top originals; and both-direction exact L-column support for **every** reserved real copy and **every** top future original, assuming the explicit, uniform original edge column `E (N+b) j = decide (j∈T)` for b<r and j∈S. It does not impose that T or its top image is a clique, nor assume full corrected B3 or automatic original extension admissibility. Five new named endpoints are pending the full hosted proof gate. The [English proof and hostile audit](numeric_h_selected_top_support_columns_english_audit.md) were committed FIRST.

## Physical carrier and conditional full gluing (10 November 2026, PR in progress)

[PR #75](https://github.com/janhubicka/lean-kk/pull/75) passed [hosted Lean run 42903693822](https://github.com/janhubicka/lean-kk/actions/runs/42903693822), including the full build, adversarial axiom-report parser self-test, and **315 exact named standard-only reports**; merged as `9e03d4e021cca4e14bcfebf65a11d393d0c9143c`. Five new physical endpoints identify the actual finite numerical-H binary L prefix with its exact reserved-copy generation-gate clique capacity.

On a separate English-first branch, `Kk/NumericHReservedPrefixGluing.lean` now states and proves three further conditional endpoints: inclusion of all real reserved prefix coordinates below the finite H carrier cut, membership in the literal `finiteNumericHL` carrier, and substitution of the *physical* capacity `if g<a then a else a+1` into the full four-pool finite gluing iff. The [English proof and hostile audit](physical_reserved_prefix_carrier_gluing_english_audit.md) were committed before the Lean source. The numerical prefix carrier subproof has an independent local pinned Lean check; the full dependent source still requires a fresh hosted gate. These are **not** claims that the required P/Q/G/W/U edge bits have been simultaneously realized by the resolved-copy construction. No manuscript green marker for that outstanding application.

## Current integration update — 10 November 2026

PR [#72](https://github.com/janhubicka/lean-kk/pull/72) (AlgorithmRun closure-parameter propagation) passed its exact-head hosted Lean gate [42485796491](https://github.com/janhubicka/lean-kk/actions/runs/42485796491) and merged as `ea4c3ee540381bd5179ac9261d07380072968c0e`. PR [#73](https://github.com/janhubicka/lean-kk/pull/73) (finite isolated-block continuation) passed hosted gate [42491952187](https://github.com/janhubicka/lean-kk/actions/runs/42491952187) and merged as `9623dde0c5c0f872548fd6da99806a00010b0703`. The **305 named endpoints** from the combined source are integrated into main; this does not discharge global diary or Ramsey-bound hypotheses.

**New separate English-first branch (not part of the 305 baseline):** `Kk/ReservedPrefixCapacity.lean` proves, *in the combinatorial pair-generation gate*, exact clique capacity of a single reserved original block prefix: `a` if `g<a`, else `a+1`, under `a≤k` and `g≤k`. The original height formulation assumes `a<r≤k+1`. Five local named transitive-axiom reports are standard-only, including the generic injective image-capacity transfer requiring exact directed Boolean L-bit equivalence; after a fresh restored Lean `4.35.0-rc3` / matching pinned Mathlib check. See [proof-first audit](numeric_h_reserved_prefix_capacity_english_audit.md). This has NOT yet been transported to actual `hPosition` / `finiteNumericHL`; hosted full project CI of the new branch is also a separate gate. No green manuscript marker for this bridge.

## Current audited status — 8 November 2026 (combined review branch)

**Local gate passed:** the combined source of [PR #70](https://github.com/janhubicka/lean-kk/pull/70), [PR #72](https://github.com/janhubicka/lean-kk/pull/72), and [PR #73](https://github.com/janhubicka/lean-kk/pull/73) passes the complete `lake build` and **305 exact named transitive-axiom reports**, using only `propext`, `Classical.choice`, and `Quot.sound`. Every requested name occurs exactly once, and the parser's missing/extra/custom-axiom rejection tests pass. The audited source is remote commit `1716d13d04f3797abc6d2529ff68adeb3d36b248`, source-equivalent to local commit `e8c2fd090bf326bbbe1fc1e562bd373b3204865e`, with identical tree `1ce1a26dfc23b0837d6aad54a1192c1fa2250977`.

The [machine-readable verification record](audits/2026-11-08-local-validation.json) contains all **305 named axiom lists**, **105 source/configuration/audit hashes**, the **11 dependency revisions**, and build/audit log fingerprints. Those hashes and dependency worktrees matched both before and after the check. The compiler is the exact pinned Lean `v4.35.0-rc3` (`470d5ce1400764999581fd26d5d72b00d990b0f4`); the restored official archive's checksum and the executor's executable-path-only workaround are recorded. No kernel or proof flags were changed.

**Subsequent hosted result:** [PR #70](https://github.com/janhubicka/lean-kk/pull/70) passed [Lean run 42483229981](https://github.com/janhubicka/lean-kk/actions/runs/42483229981) at exact head `3dfd7e0dfdc2a987326fb66f6b896bfa3d7feb25`: full build (9,486 jobs), parser self-test, and **297 exact standard-only named reports**. An independent comparison matched all 297 requested names to all 297 reports. It then merged at `fffb92e1a00a8b9978d5be245a0e4c8020eadcd1`. The actual merge and the hosted-tested PR merge have the identical tree `d3eaac3a597503068d7847e5c060d3f684413e79`, with the same parents. The merged, CI-verified code baseline is now 297 endpoints; the earlier 292 count below is the baseline from which this session began.

**Remaining hosted gates:** PR #72 and #73 stay draft and unmerged. Their completed combined **local** 305-report check does not establish their separate hosted CI result. No new manuscript green marker is assigned to these two pending branches. PR #70's five checked results may now use precise markers at its merged source revision.

| Contribution beyond the verified baseline | Named endpoints | Result |
| --- | ---: | --- |
| PR #70: numerical-H generation-one parameter closure | 5 | Combined local pass; separate hosted 297-report gate passed; merged |
| PR #72: chronological full-closure propagation | 4 | Compiled and audited in the combined source |
| PR #73: exact finite clique capacity and isolated-block continuation | 4 | Compiled and audited in the combined source |
| Total including the 292 baseline endpoints | **305** | Full local gate passed |

### Chronological parameters and actual B3 selections

[`Kk/AlgorithmRunParameterPropagation.lean`](../Kk/AlgorithmRunParameterPropagation.lean) proves monotonicity of the existing full meet/parameter closure in its allowed levels. It extends the positive-parameter theorem from a genuine original seed to a genuine original already in that closure, retaining the same ambient structure, forbidden family, seed set, and actual free levels. The implementation reuses the existing S3 theorem with the full closure as an auxiliary seed set, then collapses the repeated closure by its minimality theorem.

The actual-run theorem starts with the original available in `closure (R.I (c+1)) X`, **before cut c is tested**. When c is genuinely selected, has positive free level, lies below the source's free level, and is below the run height, the final-tail identity and closure monotonicity put its genuine Kpt parameter in every lower pre-cut closure `closure (R.I (p+1)) X`, for p<c. Source availability is therefore established at the time it is needed.

The two-step endpoint uses a real original seed, an actual complete one-upper B3 failure at c, and an actual complete two-upper B3 failure at m with `0<m<c`, `m<freeLevel(c)`, `c<freeLevel(v)` and `c<runHeight`. It **derives both selected cuts** and the intervening genuine parameter membership. Neither selection is assumed. The whole ambient L-socle and displayed complete upper types remain in the age tests. The existing K4 theorem for v=38, c=22 and m=10 now uses this general theorem and its already checked witnesses. The two concrete selections were already proved in the baseline; this change supplies a reusable chronological argument.

The [English proof and hostile audit](algorithm_run_parameter_propagation_english_audit.md) were committed before Lean at `714d7698f1b4923b8c91a81f6a9b05b23d391e62`. Independent reviews checked the chronology and absence of circular selection assumptions. The integrated numerical-H branch also repairs a strict/non-strict scan-bound mismatch in `I_eq_final_tail_of_run` by applying `Nat.le_of_lt`; its statement is unchanged. PR #70 contributes **five**, not four, endpoints.

### Exact finite isolated-block continuation

[`Kk/IsolatedBlockContinuationAge.lean`](../Kk/IsolatedBlockContinuationAge.lean) proves four endpoints using the existing directed-clique predicate, exact finite capacity, and executable clique checker:

- `finiteDirectedCliqueCapacity_attained`: an actual clique subset attains the finite capacity, including for the empty pool.
- `finitePoolCliqueCheck_false_iff_capacity_lt`: a negative exact-size clique test is equivalent to capacity below its threshold, including the zero-threshold boundary.
- `finiteDirectedCliqueCapacity_complete_join`: capacities add across a disjoint complete join, with both edge orientations specified.
- `finitePoolCliqueCheck_isolated_block_gluing_iff`: the full finite continuation test is exactly an old-plus-future test and the inserted block's capacity bound.

For the last theorem, let P be the old pool, Q the reserved pool, G the other inserted past vertices, W the future graph, and U a subset of W. Assume Q and U are disjoint, every P-to-Q and G-to-W bit is false, every Q-to-W bit in **both directions** is precisely membership in U, and the complete past `(P ∪ Q) ∪ G` is K_ell-free. Then

```text
K_ell-free (((P ∪ Q) ∪ G) ∪ W)
  iff K_ell-free (P ∪ W) and cap(Q) + cap(U) < ell.
```

Q need not be a clique. The formula uses its actual directed-clique capacity, not its cardinality. W's internal edges are arbitrary. Only Q/U disjointness is needed; an independent audit removed three redundant partition assumptions. The classification handles overlapping pools by excluding gap vertices outside W and old vertices outside Q, so it does not silently assume a partition. In this generic theorem the Boolean table `E` is ordinary graph adjacency, corresponding to numerical-H's **L** relation, not its auxiliary Kpt field E.

The [English proof and sixteen hostile checks](isolated_block_continuation_age_english_audit.md) were committed before implementation, with the strengthened contract committed at `a2c076316f20c039bd11cfaea708c59e905ce921`. A finite-maximum helper initially exhausted Lean's default elaboration budget while comparing a reconstructed executable filter. Unfolding the existing abbreviation and extracting membership at the proposition level fixed the issue; no statement or proof limit changed. The full gate then passed. Independent small directed-model checks included overlapping pools and loop bits; the manuscript's separate numerical regression passed 55 reserved-capacity cases and 2,573 labelled continuation gluings. These bounded tests support the audit and are not a substitute for the universal Lean theorem.

### Remaining mathematical obligations

The nearest local target is to instantiate the finite gluing theorem on actual numerical-H prefixes: prove the reserved-copy capacity formula with the required height condition `k ≥ r−1`, derive the support columns and every relevant gap zero for **all marked front sorts simultaneously**, and identify the resulting class of arbitrary labelled continuations with the canonical raw age bound. The existing integer graph-age canonical-cover theorem can be applied only after that identification. A one-target extension theorem does not supply the simultaneous-column premise.

The unbounded canonical schedule still needs every complete mixed-neighbourhood certificate, occurrence-independent full dependent I1/I2/I3/B3 source records including auxiliary microevents, and a common **labelled** inverse-source orbit. The separately stipulated one-point left-density interface for the fixed enumeration remains explicit. Neither the unconditional upper bound nor the independent matching lower bound is established by these additions. The 305 endpoint count measures registered checked interfaces, not a percentage of the manuscript proved.

## Previous audited status — 6 November 2026 (after PR #68)

**Reference:** [lean-kk PR #68](https://github.com/janhubicka/lean-kk/pull/68) merged as `6101b3cd222d97462127af0a8beca67d3006121f` after [full Lean CI 41941551994](https://github.com/janhubicka/lean-kk/actions/runs/41941551994) passed the complete build and **292 exact named standard-only transitive-axiom reports**, with only `propext`, `Classical.choice`, and `Quot.sound`.

**Exact incoming auxiliary E-column of TRUE finite H+:** [`Kk/NumericHTopAuxE.lean`](../Kk/NumericHTopAuxE.lean) proves that for k>0,j>0, the complete E-column at top real coordinate `ι(j,k)` is the initial segment `u<ι(j−1,k)+1`, including odd fake numeric sources. In the ACTUAL `finiteNumericH` partial structure the same iff holds if the target is inside its finite carrier, and its canonical `freeLevel(ι(j,k))` equals this cutoff. EVERY prior original i<j copied at every generation q≤k is E-positive to the top selected vertex, even when the original binary L relation is absent. This is physical L+ incidence information, not a generated fictitious E table.

**Combined genuine Henson selected L+ one-step theorem:** The previous exact PR #67 binary L column and the new incoming E/free-level column combine in one ACTUAL finite numerical H+ structure after one actual Henson selected/fresh-block stage, retaining old selected/parameter bits, all gap zeros and all-generation old/fresh nonedges. The conditional theorem explicitly requires negative old pure-unreserved/mixed-neighbourhood clique budgets, the separately stipulated exact complete-column Henson left density and at least one positive-size fresh block. The last hypothesis was added after an adversarial API audit found that the prior existential theorem does not promise selected j>0 from a merely positive base if the fresh block list is empty.

**English first and independent referee:** The [English proof and 14-point hostile audit](numeric_h_top_aux_e_english_audit.md) were committed at `12e89cfa` BEFORE Lean; the positivity correction was committed at `6d4958f8`. The independent manuscript script `verify_numeric_h_top_aux_e.py`, added to `make check-foundation`, passed **636** exact top E bits, **190** odd-fake E-positive sources, **210** prior real-generation E-positive incidences, **36** initial original-zero cases and **636** finite carrier clipping cases.

**Important actual K4 AlgorithmRun correction:** `Kk/K4ActualAlgorithmRunCut22.lean` has ALREADY proved `k4Gadget_algorithmRun_selects_cut22`: in every actual run seeded by the real top original at 38 and scanning past 22, **22 belongs to the selected level set**. The same module proves `k4Gadget_algorithmRun_q2_in_cut10_closure` (its genuine Kpt source belongs to the parameter-closed source at cut 10), while `Kk/K4ActualAlgorithmRunCut10.lean` proves `k4Gadget_algorithmRun_selects_cuts10_22`: BOTH cuts 10 and 22 are selected. Thus the K4 extra microevent is real under the specified seeded-run hypotheses, not a conjectural E-eligible cut. The remaining challenge is to handle such microevents uniformly and occurrence-independently in the canonical resolved-copy construction.

**Current next formalization:** [draft PR #70](https://github.com/janhubicka/lean-kk/pull/70) is an English-first generalisation: for height k>1, 0<i<j, generation-one original `c=ι(i,1)` has positive true free level `ι(i−1,0)+1` and lies below top free level. When c is genuinely selected into I and the top Kpt original seeded into X, the actual S3 parameter theorem forces c's complete Kpt original into the true source closure. The Henson specialization discharges finite H avoidance via the checked base age theorem. This PR's Lean CI is PENDING, so its additional 4 endpoints are not yet validated in this status entry.

**Still OPEN:** Selecting and matching all auxiliary microevents for the proposed canonical UNBOUNDED diary, actual canonical cover-age effect of physical clique gadgets, full dependent I1/I2/I3/B3 assigned source L+ records and equality of a common labelled inverse-source orbit. Unconditional upper and independent Lean lower big Ramsey bounds are not proved.

## Previous audited status — 5 November 2026 (after PR #67)

**Reference:** [lean-kk PR #67](https://github.com/janhubicka/lean-kk/pull/67) merged to `main` at `87be3df0e9f157acf6f7e5812011f3ab5ee655f8`. [Full source Lean CI 41939617150](https://github.com/janhubicka/lean-kk/actions/runs/41939617150) passed the complete build and **287 exact named standard-only transitive-axiom reports**, only `propext`, `Classical.choice`, and `Quot.sound`. This is one-step PHYSICAL numerical-H binary L geometry under explicitly displayed Henson left-density and old-neighbourhood hypotheses, not the unconditional big Ramsey upper or lower degree.

**True numerical-H full binary selected column:** [`Kk/NumericHFullSelectedColumn.lean`](../Kk/NumericHFullSelectedColumn.lean) proves that for any original `i<j`, any older generation `q≤k` and new selected TOP generation `k`, the ACTUAL numerical-H binary generation gate is ALWAYS OPEN (`q<k` or `q=k=m`). Therefore `L_H(ι(i,q),ι(j,k))=E_original(i,j)` as an EXACT directed Boolean bit, including zero and old TOP-generation copies. Under genuinely symmetric Henson original graph avoidance it holds in BOTH directions. Every actual original nonedge between old and fresh reserved originals remains absent at ALL numerical generations and in both tuple orientations.

**Actual Henson one-stage physical L gadget:** Combining the verified PR #56 genuine selected original plus arbitrary finite fresh isolated reserved clique blocks with the literal numerical-H rules gives a real one-step selected TOP binary column on EVERY older original/generation, exactly including old selected/parameter edges, fresh reserved clique positives and all skipped original-index zero passing bits. It also certifies all-generation old-to-new reserved nonedges and positive designated fresh clique-generation edges. The full theorem remains CONDITIONAL on the actual previously prescribed old mixed-neighbourhood and live-block clique-capacity certificates, and the separately stipulated exact Henson one-point left-density property.

**Adversarial evidence:** The [English proof and fourteen hostile tests](numeric_h_full_column_english_audit.md) were committed as `0ae8f474b52e59d0fe6483e8ab00f26da6eae3c4` BEFORE the Lean source. The independent manuscript referee `verify_numeric_h_full_column.py`, registered in `make check-foundation`, reconstructed the literal real-real generator across **4096** directed four-original graphs and five numerical heights, verifying **737,280** old-to-top binary atoms, **1,351,680** all-generation absent atoms, and **19,974** designated positive clique atoms.

**Still OPEN:** This exact physical binary L-atom construction has not established the intended *graph-age COVER drop* in the actual numerical-H gadget, auxiliary `E` records and free levels, selected Algorithm 5.4 I1/I2/I3 full dependent parameter closure and corrected (B3), or any common labelled inverse-source orbit. The genuine numerical-H K4 auxiliary microcut remains a critical regression. The separately proposed exact top incoming E/free-level bridge is tracked in [draft PR #68](https://github.com/janhubicka/lean-kk/pull/68) and is NOT YET validated at this snapshot.

## Previous audited status — 5 November 2026 (after PR #65)

**Reference:** [lean-kk PR #65](https://github.com/janhubicka/lean-kk/pull/65) merged to `main` as `4d8e3f8c277770fcff3811f49cebe0d5130d773a`. [Full source Lean CI 41933476329](https://github.com/janhubicka/lean-kk/actions/runs/41933476329) passed the complete build, strict parser negative/self-tests, and **283 exact named standard-only transitive-axiom reports** (only `propext`, `Classical.choice`, `Quot.sound`).

**New actual arbitrary-subfront cover-or-equality theorem:** [`Kk/CoverSubfrontIntermediateLift.lean`](../Kk/CoverSubfrontIntermediateLift.lean) defines a genuine `IsSubfrontIntegerGraphAge d ell E H` on arbitrary active sort set `E⊆Fin d` using normalized clique-multiplicity witnesses supported INSIDE E. For any genuine full `AgeCover (IsIntegerGraphAge d ell) lower upper`, it proves that the two restricted relative ages are EQUAL or form a genuine COVER in the relative age poset. This includes all overlapping E, even those containing the canonical changed support T; the earlier PR #64 disjoint/minimal-support conditions are unnecessary here.

**Exact intermediate lift (English proof first):** For any genuine relative intermediate age H between the endpoint restrictions, set the mixed RAW bounds B(S)=H(S) when S⊆E and B(S)=upper(S) otherwise. The lower full age lies below B, so the actual integer-witness canonical age G_B is a genuine full intermediate. Every saturating relative H-witness is zero outside E and respects ALL ambient B bounds: for U not inside E its contribution is on Q=U∩E; if Q empty, sum zero, otherwise `sum_Q w≤H(Q)≤upper(Q)≤upper(U)` by genuine upper-age monotonicity. Thus `G_B|E=H`, and the full cover forces G_B to equal one endpoint. The [English proof and 11-point hostile audit](cover_subfront_lift_english_audit.md) were committed at `727ced1d80679b0633026ff395f41c35921cc406` BEFORE the Lean source. No assumption that raw B is itself an age was made.

**Independent adversarial finite check:** The manuscript branch includes `verify_cover_subfront_lift.py`, added to `make check-foundation`. It reconstructs ambient normalized integer-witness ages and all genuine covers, plus zero-supported relative ages on every selected subfront; exhaustive enumeration passed **2,268 cover/subfront instances** for 2 and 3 sorts with ell=3,4.

**Remaining major gap:** Cover restriction **algebra** is complete; the physical numerical-H+ original-vertex clique-block *realization*, its prescribed old selected/parameter passing-column safety for every stage, and the parameter-closed Algorithm 5.4 I1/I2/I3/B3 microevent/source-record comparison are still unproved. The genuine common labelled inverse-source orbit and the unconditional upper and independent lower Ramsey bounds also remain open. In particular, the verified numerical-H K4 cut-10/cut-22 auxiliary B3 obstruction is not neutralized by this graph-age cover result. Do not turn the bounded resolved-copy lemma green.

## Previous audited status — 4 November 2026 (after PR #62)

**Reference:** [lean-kk PR #62](https://github.com/janhubicka/lean-kk/pull/62) merged to `main` as `88004c0c43a4d1dd7b5575ce4c6687c3c8a35e49`. [Full source Lean CI 41812326889](https://github.com/janhubicka/lean-kk/actions/runs/41812326889) passed the complete build and **271 exact named standard-only transitive-axiom reports**. This validates finite original-graph theorem interfaces, not the unconditional big Ramsey theorem.

**Deletion-only budget preservation:** [`Kk/DeactivationBudgetTransfer.lean`](../Kk/DeactivationBudgetTransfer.lean) proves that for fixed original E and `U1⊆U0`, `R1⊆R0`, the actual linked-unreserved pool shrinks, so `|R1|+cap_E(Link_E(U1,R1)) ≤ |R0|+cap_E(Link_E(U0,R0))`. A previously strict sufficient mixed-block budget remains safe. More strongly, inclusion of the COMPLETE next positive original-neighbourhood finset in the previous one transfers a negative q-clique checker across different prefix cuts. Under separately assumed Henson complete-column left density, the latter certifies a genuine later original. K4 regressions demonstrate that deletion can turn an old unsafe column into a safe one, so this implication has no converse.

**English before Lean, adversarial limits:** The [English proof and eight-point hostile review](deactivation_budget_transfer_english_audit.md) were committed as `2801cb0102f06e188fed5b965e04ed7c1e099e27` before the implementation. Both subset assumptions require actual original-edge data. An activated live reserved witness or newly positive gap/selected/parameter bit may violate them; those stages require PR #60's exact four-quadrant update plus a NEW negative capacity or full-pool check. No canonical macrodiary has been shown to satisfy these restrictions at all stages.

**Still open:** Actual event-by-event unbounded resolved-copy admissibility; exact assigned dependent I1/I2/I3/B3 source records for two same-diary occurrences; genuine common labelled inverse source and monoid orbit; unconditional upper and independent Lean lower bounds. The numerical-H K4 selected-shadow/full corrected-B3 counterexample remains an adversarial regression.

## Previous audited status — after PR #60

**Reference:** [lean-kk PR #60](https://github.com/janhubicka/lean-kk/pull/60) merged into `main` as `72f8f47bcf999b3f036151de1ee9c52db14cb31e`. [Full source Lean CI 41810904242](https://github.com/janhubicka/lean-kk/actions/runs/41810904242) passed **264 exact named transitive-axiom reports**, all using only `propext`, `Classical.choice`, and `Quot.sound`. This verifies exact finite original-graph interfaces; it does not close the unbounded Henson resolved-copy theorem or its common labelled source orbit.

**Exact four-quadrant live-set update:** The new [`Kk/LivePoolFourQuadrants.lean`](../Kk/LivePoolFourQuadrants.lean) proves that for any finite old/new unreserved positive sets `U0,U1` and old/new reserved live sets `R0,R1`, the actual directed linked pool `{x∈U1:∃ y∈R1,E(x,y)=true}` is EXACTLY the union of links between the four combinations of retained/new positive unreserved vertices and retained/new live reserved witnesses. A lost reserved witness can make an old link **disappear**, so old linked pools must not be monotonically carried forward. The generic identity requires neither graph symmetry nor `K_ell`-freeness.

**Real prefix/tag/column interface:** `linkedUnreserved_eq_updatedActualLinkedPool` specializes this identity to the actual `liveUnreserved` and `liveReservedBlock` definitions from PR #49. The old/next full original prefixes, passing columns and block-label spaces may all change. An optional old label match is supplied as an explicit comparison input; there is NO theorem here identifying genuine canonical diary source nodes. The checked `finiteNeighbourCliqueCheck_false_of_updatedActualLinkedPool_budget` uses genuine next cross-block nonedges, a negative next pure-unreserved test and per-next-block updated clique-capacity budgets to prove the COMPLETE next old-neighbourhood test negative. The conditional Henson original-realization theorem retains the exact separately assumed left-density property.

**English first; adversarial evidence:** The [English proof and 11-point hostile audit](live_pool_four_quadrants_english_audit.md) were committed at `f508ebdcd82cdcbe58ccb23cd171d6f58ff77426` BEFORE the Lean source. In the private manuscript review branch the independent `verify_live_pool_four_quadrants.py` referee was run locally and added to `make check-foundation`: **262,144** arbitrary loop-free directed three-original live-set changes (98,733 stale-link removals) and **2,654,208** actual undirected four-original two-block passing-column changes with old prefix 3 and new prefix 4 (145,968 stale-link removals). The real stale-witness and newly activated reserved/gap regressions are also Lean-checked.

**Still OPEN:** The deterministic canonical unbounded macrodiary must still produce actual next positive-neighbour sets, actual correct reserved-block matching and cross-block nonedges, negative pure-unreserved tests, and each per-next-block budget or exact PR #50 test, rather than merely being encoded by these identities. Complete dependent I1/I2/I3/B3 source-node-wise successor type assignments, equality of two labelled inverse-source orbits, the unconditional upper Ramsey bound and the independent lower bound remain unproved. The numerical-H K4 full/selected B3 obstruction remains an important negative regression.

## Previous audited status — after PR #58

**Reference:** [lean-kk PR #58](https://github.com/janhubicka/lean-kk/pull/58) merged into `main` as `d918d48dca5f696b36acfbf89dac9192df0d387b`. [Full Lean source build and strict axiom audit 41808474679](https://github.com/janhubicka/lean-kk/actions/runs/41808474679) passed **256 exact named transitive-axiom reports**, all using only `propext`, `Classical.choice`, and `Quot.sound`. Initial failed builds were purely Lean elaboration/normalization issues and were corrected without weakening theorem assumptions or adding axioms. The previous [PR #56](https://github.com/janhubicka/lean-kk/pull/56) one-step old-link-plus-fresh-block construction remains verified.

**Sharp dynamic update of old linked clique capacity:** For an ACTUAL directed Boolean original-edge table `E`, finite old linked set `L`, and a fresh original `v∉L`, let `M={x∈L : E(x,v)=E(v,x)=true}`. The checked theorem `finiteDirectedCliqueCapacity_insert_eq` in [`Kk/LinkedCliqueCapacityUpdate.lean`](../Kk/LinkedCliqueCapacityUpdate.lean) proves

`cap_E(L∪{v}) = max(cap_E(L), 1+cap_E(M))`.

It handles **both directed arcs** without assuming graph symmetry. The no-growth corollary says that if `M=∅` and `cap_E(L)≥1`, inserting `v` costs no capacity, unlike an indiscriminate +1 per linked original. A further checked finite theorem certifies the mixed pool `R∪L∪{v}` from the updated strict budget, **provided the live reserved set `R` stays fixed and the actual new linked set is precisely `L∪{v}`**. This is a conditional finite interface, not an unbounded construction.

**English first; independent hostile referee:** The [English proof and eight-point adversarial audit](clique_capacity_insert_english_audit.md) were committed as `16689068c0a3b79c880abb0162b71f1926c5018e` BEFORE the Lean module. The companion independent manuscript script `verify_link_capacity_insert.py` exhaustively checks every loop-free directed graph on four vertices, all finite old linked subsets and all genuinely fresh insertions: **131,072 exact recurrences** (**80,820 no-growth** and **50,252 growth**), plus positive and negative K4 original-edge regressions. The script was added to the manuscript's `make check-foundation`. The PR's Lean theorem is a genuine generic proof, not a finite computation.

**Outstanding real geometric induction:** The next selected vertex may have a DIFFERENT subset of live reserved originals, and there may be additional intervening gap originals. No proof yet identifies the actual next linked pool with one fixed `L∪{v}` or relates the resulting capacities to the intended canonical graph-age cover sequence. The global numerical-H resolved-copy schedule, full parameter-closed assigned I1/I2/I3/B3 source-node comparisons, common labelled inverse-source orbit and unconditional Ramsey upper/lower bounds remain OPEN. The real K4 cut-10/cut-22 corrected-B3 obstruction remains a regression test.

## Previous audited status — after PR #56

**Reference:** [PR #56](https://github.com/janhubicka/lean-kk/pull/56) is merged to `main` as `64000bd29a1df17f7fe4e8d87504e888c7d0e6d4`. [Full source build and strict axiom audit 41790461406](https://github.com/janhubicka/lean-kk/actions/runs/41790461406) passed **247 exact named transitive-axiom reports** with only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the displayed conditional theorem, not an unconditional big Ramsey degree.

**One complete Henson successor stage with OLD block links and NEW blocks:** In [`Kk/LinkedAndFreshStage.lean`](../Kk/LinkedAndFreshStage.lean), `henson_leftDense_later_selected_after_fresh_blocks_of_link_capacity` combines the PR #54 genuine old prefix negative-neighbourhood certificate from clique-capacity budgets with PR #52's existence of arbitrary finite families of fresh isolated reserved original cliques and one later selected original. The selected original preserves **all certified prescribed old positive passing bits**, including actual links to older reserved and selected/coding parameter vertices, sees exactly the new reserved blocks above the old cut, and has zero passing bits to every intervening outsider. The new theorem further proves every NEW reserved original is nonadjacent in both orientations to EVERY original below the old cut. The original Henson graph is not edited.

**English before Lean, adversarial boundary:** The [English proof and 10-point hostile audit](linked_and_fresh_stage_english_audit.md) were committed at `ada31141070cc8f5a949575546bdf0516907f93d` BEFORE the Lean source. In particular, the new selected original can increase clique capacities for the NEXT selected stage; a one-step construction does not prove all subsequent old link-capacity budgets automatically. The `ell-1` fresh block-size inequality is strict, and all original older selected/parameter vertices are included in the actual prior certificate.

**Still genuinely open:** Prove that the intended deterministic UNBOUNDED resolved-copy macrodiary passes the actual pure-unreserved and per-old-block mixed certificates at EVERY stage, not just under explicit hypotheses. Then establish equality of full assigned source-node-wise I1/I2/I3/B3 data, the common labelled inverse-source orbit, the unconditional Ramsey upper bound, and the independent Lean lower bound. The numerical-H K4 selected-only-to-full B3 counterexample remains relevant and cannot be bypassed by these old-original geometry lemmas.

## Previous audited status — after PR #54

**Reference:** [PR #54](https://github.com/janhubicka/lean-kk/pull/54) is merged to `main` as `117daf353d9b67fa3c54ba2890e6a137b97b41ca`. The [source full build and strict axiom audit 41789150529](https://github.com/janhubicka/lean-kk/actions/runs/41789150529) passed **246 named exact transitive-axiom reports**, all using only `propext`, `Classical.choice`, and `Quot.sound`. This certifies the precise conditional theorem endpoints, **not** an unconditional big Ramsey degree.

**Genuinely later selected vertices:** `Kk/LinkedCliqueCapacity.lean` computes the maximum directed clique cardinality in the **actual** old linked-unreserved set for a reserved block, instead of crudely bounding that set's vertex cardinality. If the number of live reserved neighbours plus this clique capacity is strictly below `ell-1` for each block, and the exact pure-unreserved checker is negative with genuine old cross-block nonedges, PR #50's exact decomposition yields a negative COMPLETE selected-neighbourhood checker. The theorem `henson_leftDense_realizes_later_selected_of_link_capacity` then selects a genuine later original under the separately stipulated Henson complete-column left-density property, even when older selected originals and coding parameters are positively adjacent to older reserved vertices.

**English-first and adversarial evidence:** The [English proof and 10-point hostile audit](linked_clique_capacity_english_audit.md) were committed at `396662b279aca3826388f84274df03daafb6cd57` **before** Lean source. Exact `K_4` positive/negative regressions show the advantage over raw cardinality: one reserved original links to two older selected originals which are independent, so linked clique capacity is one even when linked cardinality is two; inserting their missing mutual edge makes the next selected vertex unsafe. The companion independent referee in the manuscript branch, `verify_link_capacity_budget.py`, tested **181,760** four-original two-block cases with **109,233** sufficient-budget instances and no counterexample.

**Critical limitation:** This is a **sufficient local budget**, not an exact equivalence or a proof that the proposed infinite resolved-copy macrodiary satisfies the budgets. The nontrivial missing application is to prove negative complete mixed-neighbourhood tests at each ACTUAL recursive stage. Full assigned upper `L^+` successor types, I1/I2/I3/B3 dependent parameter-closed envelopes, common labelled inverse-source orbit, unconditional upper-bound and independent Lean lower-bound remain OPEN. The verified numerical-H `K_4` corrected-B3 counterexample continues to prohibit selected-age-shadow `=>` full B3 shortcuts.

## Previous audited status — after PRs #51–52

**Reference:** `main` at `efee866dcac9799c4e3240e40ce3a92245e2e893`. [Full CI on merged main 41781999792](https://github.com/janhubicka/lean-kk/actions/runs/41781999792) succeeded. [PR #52 source build and strict audit 41781628701](https://github.com/janhubicka/lean-kk/actions/runs/41781628701) checked **239 exact named transitive axiom reports**, permitting only `propext`, `Classical.choice`, and `Quot.sound`. This is validation of the theorem interfaces and their stated hypotheses, **not** validation of the final big Ramsey degree theorem.

**English-first finite block geometry:** [PR #51](https://github.com/janhubicka/lean-kk/pull/51), merged as `4b39c80c79694b2deb1be68c9cc2335312a468be` after [full CI 41756353162](https://github.com/janhubicka/lean-kk/actions/runs/41756353162), establishes any finite ordered family of *genuine original-index* reserved cliques of sizes `r<ell`, with all earlier-outsider nonedges (including enumeration gaps) and actual two-direction cross-block nonedges. The regression `full_reserved_block_forbids_selected_column` proves that a future selected vertex seeing the entire block needs the stricter `r<ell-1` condition.

**Sharpened complete-neighbourhood theorem:** [PR #52](https://github.com/janhubicka/lean-kk/pull/52) (merged as `efee866dcac9799c4e3240e40ce3a92245e2e893`) first committed [an English proof and adversarial audit](last_neighbour_isolation_english_audit.md), then formalized `finiteNeighbourCliqueCheck_false_of_last_isolated`. A hypothetical `q>0` neighbour-clique has a largest original index `y`. If `y` lies in the old prefix, the old negative certificate rules it out. Otherwise it is a newly reserved neighbour; every earlier member of the alleged clique must lie in its small isolation block `S_y`, contradicting `|S_y|<q`. This checks the **entire actual original/parameter neighbourhood** without inferring an invalid selected-graph-age to full-B3 projection.

**One genuine selected successor after an arbitrary finite fresh block family:** `henson_leftDense_selected_after_fresh_block_family` combines PR #51 with that maximal-neighbour argument and the separately stipulated exact `OnePointLeftDense E ell` property. It chooses a later original of the *unchanged fixed Henson enumeration* with exactly the prescribed old-prefix positive column, positive bits to the freshly reserved blocks, and zeros through every intervening gap, in both directed orientations.

**Hard boundary:** This is a **single** selected extension after *freshly isolated* blocks; it cannot simply be iterated when newer selected vertices may be adjacent to older reserved blocks and older selected vertices linked to those blocks. For the proposed unbounded recursion, negative pure-unreserved and per-block *actual mixed interaction-pool* tests must still be proved at every stage. Full I1/I2/I3/B3 dependent parameter closure, occurrence-independent assigned upper L+ successor types, the genuine common labelled inverse-source orbit, the unconditional upper bound, and the independent Lean lower bound all remain open. The numerical-H K4 corrected-B3 counterexamples remain essential regression tests.

## Previous audited status — 3 November 2026

**Reference:** `main` at `7da043de5c0987a554fa409614252d9c84bf41f4`.
Its source tree `2542d123ada41ae6825a4833a915e54f45de431b` passed [full Lean build and strict axiom-check run 41741406897](https://github.com/janhubicka/lean-kk/actions/runs/41741406897) on 4 November (233 exact named reports). The tested PR head and merged main have identical source trees. This is an audit of the stated Lean endpoints, **not** a completed proof of the big Ramsey degree.

**Kernel-checked components:** finite-family type-respecting Ramsey transfer; genuinely labelled carrier/action interfaces; Henson forbidden-family translation; numerical-H selected-original and full AlgorithmRun I3 clique/signature bounds under their displayed hypotheses; integer-witness graph-age normalization, canonicalizer universal properties, monotonicity, small-function identity **with nonempty domain qualifications**, and the canonical selected-front cover-block algebra.

**Current geometric progress (4 November):** [PR #47](https://github.com/janhubicka/lean-kk/pull/47), merged as `a3d1e22631bc9505c4c1157865150e1703da48c1`, proves a complete neighbourhood reduction for the FIRST selected original following a genuinely isolated but potentially noncontiguous reserved block, and constructs the actual reserved original clique plus first selected successor from any safe older passing column. [Full CI 41666361540](https://github.com/janhubicka/lean-kk/actions/runs/41666361540) passed 217 strict named axiom reports. [PR #48](https://github.com/janhubicka/lean-kk/pull/48), merged as `c0618228110f267c182e5a05ce5839dfe60531be`, independently checks the ACTUAL numerical-H generation gate, including designated reserved clique-positive edges and both directions of the reserved-to-top-selected edges. [Integration CI 41668989434](https://github.com/janhubicka/lean-kk/actions/runs/41668989434) passed 221 strict reports.

**Later selected vertices with older block links (4 November):** [PR #49](https://github.com/janhubicka/lean-kk/pull/49), merged as `0e35e3b802fab03ec51f8bb842a266c22504bc29`, proves every actual mixed clique meeting reserved vertices lies in the *unique block's live interaction pool* (active reserved vertices plus unreserved old neighbours actually linked to them). The pure-unreserved finite clique test plus sufficiently small per-block interaction pools is sufficient for a safe new selected original, including genuine left-dense realization. [Full CI 41740174401](https://github.com/janhubicka/lean-kk/actions/runs/41740174401) passed 225 standard-only named reports.

**Exact finite decomposition, not merely cardinal bounds (4 November):** [PR #50](https://github.com/janhubicka/lean-kk/pull/50), merged as `7da043de5c0987a554fa409614252d9c84bf41f4`, proves that under genuine cross-block nonedges the COMPLETE old-neighbourhood `K_(ell-1)` test is negative **iff** the pure-unreserved finite test and each live block interaction-pool finite clique test are negative. The criterion applies to later selected vertices whose older selected neighbours may already be linked to reserved blocks, and yields an actual new original under the fixed Henson left-density property. The executable five-old-neighbour `K_4` regression has only two live block-interaction vertices and illustrates why cardinal-only bounds were unnecessarily strong. [Full CI run 41741406897](https://github.com/janhubicka/lean-kk/actions/runs/41741406897) passed **233 exact named standard-only axiom reports** (with negative self-tests for the checker).

**Unproved after these bridges:** the proposed *unbounded* resolved-copy schedule has not been shown to satisfy the exact per-stage finite tests or to preserve the required cross-block original incidences at EVERY stage. Neither exact finite decomposition nor numerical-H positive-edge copying identifies the full dependent I1/I2/I3/B3 closure, same-diary complete parameter-closed envelopes, a common labelled inverse-source orbit, or the unconditional Ramsey upper/lower bounds.

**Refuted shortcut, retained as regression:** selected-front graph-age equality cannot be used to infer full parameter-closed corrected (B3). The numerical-H K4 cut-10 example with auxiliary original 22 and selected original 38 refutes the unrestricted inference; the two-sort examples also show the abstract problem. The `GraphAgeShadow`, `K4AuxiliaryShadow`, `UniformAuxiliaryShadow` and `K4FullVsMarkedB3` modules are *negative tests*, not alternative upper-bound proofs. Do not delete them merely for being unused in a positive proof.

**New formally proved finite-geometry bridge (3 November):** [PR #38](https://github.com/janhubicka/lean-kk/pull/38) proves the exact one-point K_ell-free neighbourhood criterion, including all older parameter vertices; [PR #39](https://github.com/janhubicka/lean-kk/pull/39) proves that cross-block nonedges reduce every old clique to either pure unreserved vertices or one reserved block **plus arbitrary unreserved vertices**, and derives a sound blockwise mixed-neighbourhood extension test. Both are merged and axiom-checked, as is main. These are mathematical criteria, not an existence construction for a globally resolved Henson copy.

**New verified exact finite-neighbourhood certification (3 November):** [PR #40](https://github.com/janhubicka/lean-kk/pull/40), merged as `442cc1e745e8becc51b1b12f07118fca8db5710e`, adds a computable exhaustive finite old-neighbourhood clique checker and proves it sound and complete for one-point K_ell-freeness. The actual four-original K4 base has a negative certificate; adding parameter-to-block edges to form a triangle gives a positive certificate and a genuine forbidden K4. [Full CI run 41635293405](https://github.com/janhubicka/lean-kk/actions/runs/41635293405) passed **180** standard-only named axiom reports.

**New verified finite-schedule induction (3 November):** [PR #41](https://github.com/janhubicka/lean-kk/pull/41), merged as `115647925356e4da4fe3626374f2a3384365e083`, proves for a symmetric irreflexive graph that its whole finite prefix is K_ell-free **iff every earlier original insertion passes the complete finite-neighbourhood certificate**. The actual K4 four-original table satisfies all four stage certificates. [Full CI run 41636829920](https://github.com/janhubicka/lean-kk/actions/runs/41636829920) passed **186** exact transitive-axiom reports, all among `propext`, `Classical.choice`, and `Quot.sound`. The PR head and merged main have the identical source tree `3cc455be3b6c21b5403b70edd6b7c21cc6122521`.

Neither theorem establishes that every extension in the proposed **unbounded** resolved copy has a negative certificate, nor the full dependent I1/I2/I3/B3 envelope comparison or common labelled inverse-source orbit.

**New verified safe reserved-block insertion (3 November):** [PR #42](https://github.com/janhubicka/lean-kk/pull/42), merged as `63beeb7bbf79fb6efbbc1c2ca2522998381d8d98`, explicitly appends an isolated clique of `r<ell` new originals by one-point steps. It proves old-original atom preservation, both the internal positive clique edges and the zero edges from old parameters to the block, and K_ell-freeness at **every intermediate stage**. The complete finite-neighbour cardinality condition is checked, not inferred from a selected age shadow. [Full CI run 41639561008](https://github.com/janhubicka/lean-kk/actions/runs/41639561008) passed 195 strict named standard-axiom reports. This applies to **isolated** blocks, not to extensions with extra prescribed old-parameter edges.

**New actual-index existence bridge, conditional on left density (3 November):** [PR #43](https://github.com/janhubicka/lean-kk/pull/43), merged as `d6b5d7d81195bffa1c774209dbd260dda18d988f`, constructs a genuine finite set of later reserved ORIGINAL INDICES inside one fixed ambient graph, with all pairwise positive clique edges and all earlier nonreserved directed edges absent. Its hypothesis `SmallCliqueLeftDense` explicitly requires finding a later original whose complete passing column equals the prescribed small old neighbour set (including intervening indices). That hypothesis **has not been instantiated for the manuscript's particular fixed Henson enumeration**, and it does not follow from K_ell-freeness alone (a negative counterexample is Lean-checked). [Full CI run 41640693600](https://github.com/janhubicka/lean-kk/actions/runs/41640693600) passed 198 exact named transitive-axiom reports, all standard.

**Complete simple graph signature for the isolated block (3 November):** [PR #44](https://github.com/janhubicka/lean-kk/pull/44), merged as `06f35961e0db5eb8ab2fdd5bf4556e0935b65f76`, closes a previously separate graph-language obligation. The construction preserves **symmetry of all directed edges and false diagonals**, both orientations of every old-to-reserved nonedge (under original symmetry), and full-prefix K_ell-freeness. The packaged endpoint `appendIsolatedCliqueBlock_graph_valid_prefix` checks exactly these conditions; it makes no claim of a global Fraïssé copy. [Full CI run 41642395383](https://github.com/janhubicka/lean-kk/actions/runs/41642395383) passed 204 standard-only transitive-axiom reports (including parser negative tests). Its tested head and merged commit have the same source tree `89e5e848d7095d8ab841a7e1c92130e07edace5b`.

**The stated left-dense enumeration now bridges to genuine originals (3 November):** [PR #45](https://github.com/janhubicka/lean-kk/pull/45), merged as `e43e81169cd9e5c7984c2b0eca118e1fab8cfa61`, gives a literal complete-column Boolean formulation `OnePointLeftDense` of the manuscript's one-point left-density condition, proves that a **negative complete finite-neighbourhood certificate** produces an actual later original with all intervening nonedges, and derives PR #43's `SmallCliqueLeftDense` hypothesis from one-point left density plus K_ell-freeness of all prefixes. [Full CI 41649826866](https://github.com/janhubicka/lean-kk/actions/runs/41649826866) passed **207** exact standard-only named axiom checks.

**Prefix safety now follows from the actual normalized Henson age (3 November):** [PR #46](https://github.com/janhubicka/lean-kk/pull/46), merged as `b4d8a16466d4632c4f09b7c719a7658d6e4be9c9`, derives every old prefix's K_ell-freeness from the **existing** normalized forbidden-family theorem by sorting any finite forbidden clique into a strict increasing Fin ell-indexed one. The named result `henson_leftDense_exists_reserved_originals` now obtains genuine isolated reserved originals beyond any given cut from **normalized Henson avoidance plus `OnePointLeftDense`**, with no separate small-set density or per-prefix freeness assumptions. The companion `henson_leftDense_realizes_certified_original` realizes any later selected original whose **full** old-neighbourhood certificate is already known negative. [Full CI 41651031332](https://github.com/janhubicka/lean-kk/actions/runs/41651031332) passed **212** named axiom reports, all standard; tested and merged commits have the same tree `550972870f92742e38d6e2016ab3c2df52b7dafa`.

**Scope and outstanding model-level identification:** `OnePointLeftDense` is the exact *edge-table* formulation of the one-point extension property that the manuscript assumes for its **chosen** left-dense enumeration. This work does not construct that enumeration within Lean or formalize a Fraïssé-isomorphism carrying the manuscript's abstract embedding definition to the Boolean `E`. The previous extra `SmallCliqueLeftDense` premise is discharged assuming this stated left-density property. The still-open hard task is proving that the specific proposed later selected-vertex columns have **negative full mixed-neighbourhood certificates**, before handling their parameter-closed Algorithm 5.4 I1/I2/I3/B3 data and common labelled source orbit.

**Still missing after PRs #42–43:** certify the exact density property for the fixed enumeration or replace it with a demonstrably available weaker extension interface; handle reserved auxiliary steps requiring extra edges to old selected/parameter originals; then check **later selected originals** adjoining gadget blocks and older parameters. These are independent of and precede the cross-occurrence full I1/I2/I3/B3 comparison and common labelled source orbit.

**Sharper remaining geometry:** in each proposed recursive stage, supply the actual old original/parameter incidence table, prove that all tagged reserved copies satisfy the cross-block hypotheses, and discharge both the pure-unreserved and the per-block **mixed with unreserved** neighbour-clique tests. The existing `HBlockNonedges` theorem handles real reserved-copy nonedges under explicit hypotheses, but it does not verify the mixed tests or full dependent I1/I2/I3/B3 closure.

**Outstanding substantive gaps:** global admissibility of mixed original/parameter/clique-block extensions; synchronization of full dependent I1/I2 and ordinary L+/E successor assignments for equal macrodiaries; full I3 comparison at every selected and unrecorded microlevel; common labelled inverse-source orbit; unconditional Ramsey upper bound and matching lower-bound formalization. The verified all-generation AlgorithmRun I3 clique-capacity theorem does **not** need to be reproved, and does **not** close those gaps.

**CI verifier repair (3 November):** the previous workflow's `grep -Eq 'sorryAx|unknownConstant|axiom.*Kk\.'` did not inspect the transitive axiom *list* and would not reject a new axiom named outside `Kk`. The replacement checker parses every `#print axioms` request and corresponding Lean report, rejects missing/duplicate/extra reports, and whitelists only `propext`, `Classical.choice`, and `Quot.sound`. Its parser has negative self-tests. The current merged-main run checks **233 exact named transitive-axiom reports**, all within that whitelist, with negative self-tests for the report parser.

**Adversarial cleanup rule:** remove superfluous assumptions and obsolete *arguments*, not tested counterexamples. Historical status entries below are date-specific and often say “pending” about PRs which have since merged. They are evidence of the validation process, not the current task list. Manuscript black-text corrections belong in TODOs and a separate correction note; only olive prose is edited directly.

## Dated historical validation log

## 28 October — ordinary L-profile, bounded forbidden cores and cut-star localization

Three new stacked PRs have passed complete full Lean builds and the
named transitive-axiom audit, all using only
`[propext, Classical.choice, Quot.sound]`.

- [PR #5](https://github.com/janhubicka/lean-kk/pull/5),
  [run 40696464930](https://github.com/janhubicka/lean-kk/actions/runs/40696464930),
  code `a3188b45e7c16771c7ac5f12a62d8e3dd82bbfd2`:
  `correctedB3_of_Lprofile_dominance`,
  `failed_markedB3_of_Lprofile_dominance`,
  `correctedB3_iff_of_equal_Lprofiles`. A marked corrected-B3
  test dominates the full test if it covers each ordinary initial
  L-socle and each allowed full complete upper L-reduct type.
  This conditional transfer needs no equality of auxiliary E atoms
  in arbitrary continuation witnesses.
- [PR #6](https://github.com/janhubicka/lean-kk/pull/6),
  [run 40697939142](https://github.com/janhubicka/lean-kk/actions/runs/40697939142),
  code `1017a99fdd370f4e83067973f200d673a5a66cc5`:
  `normalized_avoid_without_of_future_restriction`,
  `henson_selectedB3_failure_has_small_clique_core`.
  Every failed actual selected-original corrected B3 has a
  finite L-only continuation with its full old socle and only
  the future vertices of one K_ell clique. The clique contains
  the tested cut, leaving at most ell-1 future vertices.
- [PR #7](https://github.com/janhubicka/lean-kk/pull/7),
  [run 40698495262](https://github.com/janhubicka/lean-kk/actions/runs/40698495262),
  code `33993901dba31e0110490ecbc791415244ce3ecb`:
  `clique_core_upper_name_adjacent_to_cut`,
  `clique_core_upper_names_local_of_cut_nonedges`,
  `henson_failed_selectedB3_has_cut_local_small_core`.
  Every future clique vertex of ANY allowed L-only B3 continuation
  has a selected named actual-H original adjacent to the tested
  cut. Excluding names by ACTUAL cut-to-original nonedges is
  therefore valid despite unconstrained future-to-future W edges.
  Support-locality retains the explicit outside-support nonedge
  hypothesis; the canonical resolved gadget has not yet been
  shown to satisfy it for all full parameter-closed names.

New [PR #8](https://github.com/janhubicka/lean-kk/pull/8) checks
the exact numerical H free-cut threshold for a later
generation-1 auxiliary original at an earlier generation-0
gadget cut. Until CI passes this numerical identity is **not**
a kernel validation marker. Even if verified, free-cut eligibility
does not imply `closureSelectedOriginal` membership; the
I1/I2 parameter-closure record must still be studied.

**Adversarial obstruction:** in K4, the two-sort age states
`(F(x),F(z),F(x,z))=(2,1,3)` and `(2,1,2)` are valid
and form a true cover while leaving the selected x shadow
unchanged. Thus a future auxiliary name that is present in
the full corrected-B3 pool can cause a hidden age drop.
The K_k resolved construction may exclude its membership or
otherwise represent its age event, but abstract graph-age
axioms do not. This is a finite-state computation, not a
Lean proof of a failure of the resolved copy.

**Still pending:** full `closureSelectedOriginal` name
classification at canonical gadget levels; actual selected
shadow B3 projection; same-diary marked labelled inverse
sources; final big Ramsey upper and lower bound validation.


## 28 October — all-generation clique witnesses and sharp numerical-H I3 bound

Two stacked Lean PRs now pass complete `lake build`, named `#check`,
and `#print axioms` for every new endpoint:

- [run 40607378504](https://github.com/janhubicka/lean-kk/actions/runs/40607378504),
  at commit `a1467ebd4968a28b9c418676d9296aa954af2bff`:
  `Kk.hNumericBinary_symmetric_of_base`,
  `Kk.henson_finiteNumericH_binary_symmetric`, and
  `Kk.henson_selectedB3_failure_has_clique_witness`.
- [run 40608111843](https://github.com/janhubicka/lean-kk/actions/runs/40608111843),
  at commit `fa3d622900e9304b1aad54b2296d32a690e76271`:
  `Kk.henson_any_generation_B3_has_clique_higher_signature` and
  `Kk.henson_algorithmRun_all_I3_levels_card_le_higher_clique_capacity`.

The exact transitive axiom lists are
`[propext, Classical.choice, Quot.sound]`.

**New zero-generation argument.** The literal directed binary relation
of numerical H is symmetric everywhere when the base graph is symmetric.
In a genuine selected-original corrected-B3 failure, an actual finite
witness W has the same initial L socle, and every upper W vertex has
the complete directed L-type of a named actual original. Its cut-deleted
reduct avoids the complete four-pattern Henson forbidden family.
Thus a forbidden asymmetric pair would have to cross the tested cut,
where complete type equality and ambient symmetry preclude it.
A non-neutral singleton also cannot be the witness, by the checked
proper lower/upper-cut lemma. Hence an actual K_ell clique witness exists
even for g=0; the rank/cardinality argument g+2>=3 is no longer
needed to classify this case.

**Same witness; sharp counting.** The relocated clique witness has
all its chosen upper original names at strictly higher H generation
m>g, including g=0. Restrict its signature to that subpool of the
**same actual final-stage finite pool** constructed from the complete
AlgorithmRun, and apply the verified one-pattern signature-collision
theorem. For all `0 <= g < k`:

`|I3_g| <= (M_g+1)^ell`,

where `M_g` counts exactly those higher-generation final-pool names.
Top-generation I3 events are already excluded by a separately checked
theorem (subject to the displayed I1/I2 absence premises).

**Critical limits.** These theorems concern full selected-original
corrected B3 and actual Algorithm 5.4 I3 levels. They DO NOT prove
that every auxiliary B3 witness of the special resolved diary is
captured by the marked active graph-age shadow. Further, the
actual-original cross-block nonedge lemma controls real H cliques,
not free future-to-future edges in arbitrary B3 continuations.
The common marked labelled inverse source for two occurrences of a
diary, the final Ramsey upper bound, and the published lower bound
remain pending. No new validation certificate is assigned to them.


## 27 October — sharp positive-generation fixed-clique I3 bound

[Full Lean run 40518293067](https://github.com/janhubicka/lean-kk/actions/runs/40518293067)
at commit `b704e3ca5b828a9d2c972e453e6a69cbe006b4e1` passed
`lake build`, named `#check` and transitive `#print axioms`
for both new endpoints. Their only axioms are
`[propext, Classical.choice, Quot.sound]`.

- `Kk.henson_positive_generation_B3_has_clique_higher_signature`
  chooses **one actual finite L-only K_ell forbidden continuation**
  witnessing failure of corrected B3 at a selected-original stage
  of positive numerical-H generation g. It uses the exact I3
  relocation and chosen-original theorem to establish that
  every upper name of that SAME witness has generation m>g,
  while retaining one fixed clique-pattern family index.
- `Kk.henson_algorithmRun_positive_I3_levels_card_le_higher_clique_capacity`
  constructs the actual complete parameter-closed AlgorithmRun
  selected stage and one SAME finite final-stage original pool
  for all tested levels, restricts witness names to its strictly
  higher-generation subpool, and applies the kernel-checked
  fixed-pattern signature collision bound. Its conclusion is

  `|I3_g| ≤ (M_g + 1)^ell` for `0 < g < k`,

  where `M_g` is the cardinality of the exact subpool of
  final-stage original names at generations strictly above g.

This closes the earlier **quantitative combination gap** between
the previously checked full-family higher-generation capacity and
the whole-pool clique-only capacity. It does not classify the
g=0 forbidden signatures, which can still include normalized
asymmetry patterns. The selected-original versus active diary
branch projection, the common labelled diary source, and
optimality remain separate, unverified obligations.

The manuscript `kk.tex` now states and cites the final bound
with a green pinned validation marker, while retaining the
unresolved full auxiliary (B3)-to-selected diary comparison
as an explicit TODO.


## 26 October — positive-generation forbidden cliques and restricted signatures

[Full Lean CI run 40400450373](https://github.com/janhubicka/lean-kk/actions/runs/40400450373)
at `1c2ed2ceaf186bcf8cafc30069994936ea76e548`
passed `lake build` and the named transitive axiom audit.
Each named endpoint uses only `[propext, Classical.choice, Quot.sound]`.

- `Kk.henson_forbidden_pattern_large_is_clique`: among the four
  normalized Henson forbidden patterns (loop, two asymmetries,
  symmetric clique), only the clique has cardinal at least 3.
- `Kk.henson_positive_generation_B3_has_clique_witness`: a
  failed corrected B3 test at **positive numerical-H generation**
  in the genuine selected-original pool has a finite forbidden
  L-continuation witnessing failure of the clique, not merely
  one of the other normalized directed patterns.
- `Kk.henson_algorithmRun_positive_I3_has_clique_witness`:
  the same conclusion for a true nonstructural I3 level of the
  full parameter-closed Algorithm 5.4 run. The closure-to-original
  witness mapping is constructed from the actual run.
- `Kk.i3Levels_card_le_fixedPattern_capacity`: an exact
  general I3 signature collision bound for witnesses whose
  forbidden-family index is fixed, namely
  `levels.card <= (M+1)^(patternCard)`. No independently
  assumed signature injectivity is added.

The already verified `g+2 <= ell` generation-size bound and
these results justify the mathematical refinement: for
`g>=1`, all responsible forbidden signatures belong to
the `K_ell` index. The general fixed-index counting theorem
provides the expected `(M_g+1)^ell` target.

**Not yet connected in Lean:** the single-clique-index witness
must be constructed with only the **strictly higher-generation
selected-original names**, simultaneously for every level of
the actual run. Until this adapter is formalized, the sharper
bound remains a mathematical deduction in the olive manuscript,
not a kernel-checked composite theorem.

**Also unresolved:** generation `g=0` may a priori have
asymmetric-pair forbidden witnesses. Excluding them requires
a genuine crossing-symmetry argument for the full finite L-only
age-test continuation, not just symmetry of the ambient H
socle. Most importantly, even the strengthened I3 signatures
do NOT prove the diary's common labelled source or exact upper
bound: the full auxiliary-to-selected age projection remains open.


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

## 22 October — independent B3 shadow counterexample and cut rigidity

[Lean run 39805797998](https://github.com/janhubicka/lean-kk/actions/runs/39805797998)
on commit `7e528b761b94b8e2b6a3e875b5154b6bf98aa446`
passed `lake build` and the complete named axiom audit. New endpoints:

- `Kk.fullBefore_valid` and `Kk.fullAfter_valid`:
  exact consistency witnesses for two K3 graph-age functions on
  selected type x and auxiliary type z, with singleton bounds 1
  and joint bounds respectively 2 and 1.
- `Kk.fullAfter_covers_fullBefore` and
  `Kk.selected_shadow_does_not_detect_cover`:
  the reduction is a genuine age cover and leaves the selected
  singleton x unchanged. This demonstrates that the manuscript's
  old full-(B3)-to-selected-shadow implication does NOT follow
  from the graph-age axioms alone.
- `Kk.vertex_eq_of_common_top_and_size` and
  `Kk.labelled_sources_eq_of_common_top_and_cuts`:
  for genuine finite L+/E prefix codes a shared source top
  and equal selected source lengths determine the labelled
  source copy exactly.

All named theorem dependencies are
`[propext, Classical.choice, Quot.sound]`. The olive
boring-level lemma has been repaired to expose its
additional **auxiliary-witness projection** hypothesis, which
still requires verification in the specially resolved H copy.
Neither the genuine counterexample nor the common-top/cuts
criterion is a completed diary comparison.

## 22 October — numerical H cross-block nonedges

[Full Lean Actions run 39806546276](https://github.com/janhubicka/lean-kk/actions/runs/39806546276)
passed build and axiom checks at
`891dfc7891458e30c195e7cb69e0e275d932dbfe`.
The new module `Kk/HBlockNonedges.lean` uses the **actual**
`hNumericBinary`, `finiteNumericHL`, and `infiniteNumericHL`
from the pinned successor library.

- `numericH_preserves_original_nonedge`
- `finiteNumericH_preserves_original_nonedge`

prove that for distinct original indices in increasing order,
an absent original directed binary atom stays absent between
**every pair of generation copies**, regardless of their
generation gate, in the countable and finite numerical H
structures. Standard axioms only.

In the manuscript the reserved originals for different canonical
cover blocks are chosen mutually nonadjacent. These theorems
justify the claim that their generated H copies remain
nonadjacent, provided the original nonedge choices have been
made. They are relevant genuine structural input to the full
(B3) projection, but do not settle witnesses inside one block
or those involving E and parameter-closed auxiliary types.

## 22 October — actual numerical H clique-block support locality

[Lean run 39808546237](https://github.com/janhubicka/lean-kk/actions/runs/39808546237)
at `c74426b3a464c0a18d6afb6a95ce7f0b7d5718fb`
passes the full build and named transitive axiom audit
(standard `[propext, Classical.choice, Quot.sound]`).

The true `hNumericBinary` relation and the preceding
nonedge-preservation theorem prove:

- `Kk.reserved_H_clique_one_block`: in a complete directed
  clique of genuine reserved auxiliary H-generation vertices,
  the vertices use only one witness-block index whenever
  distinct blocks were originally chosen mutually nonadjacent.
- `Kk.reserved_H_aux_selected_clique_support`: if a reserved
  original has no base edge to selected future originals
  outside its declared block support, any selected future
  vertex lying with it in a generated positive clique must
  belong to that support, at ALL permitted generations.
- `Kk.reserved_H_clique_one_block_and_selected_support`:
  the combined conclusion for a clique of reserved
  auxiliary originals and selected future originals.

These endpoints verify the **real numerical H vertex**
part of block locality. The critical remaining (B3)
application is to show arbitrary allowed L-continuation
witnesses, including auxiliary parameter types, reduce
to such genuine reserved-generation configurations.
That implication is not among the checked statements.
The existing pinned successor theorem
`numericI3_forbidden_copy_forces_last_lower_rank`
may help exclude nondesignated generations, once its
named-original upper-type hypotheses are extracted
from the full parameter-closed witness data.

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
