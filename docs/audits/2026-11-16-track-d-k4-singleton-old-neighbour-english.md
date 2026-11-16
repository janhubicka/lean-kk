# Track D — singleton capacity ≤2 iff a genuine old Q neighbour exists
16 November 2026. English proof and 16 adversarial checks BEFORE Lean.

## The exact manuscript step being audited

In the olive small-independent upper proof, the "no omitted I2 fork" argument compares one selected positive TOP type with the cap or an auxiliary negative future type. It argues: when the omitted event gives the selected type a new neighbour, its permitted singleton clique capacity becomes at most two; since the event preserves the selected singleton age, the capacity was already at most two; therefore **an ACTUAL OLD Q neighbour v** existed before that whole event. The generation-zero numerical copy v_0 then distinguishes these two dependent upper L+ types *before* the omitted cut.

The implication "singleton age≤2 ⇒ actual old neighbour" is not a purely formal graph-age axiom: it relies on the genuine finite old-prefix Henson K4 extension-age formula. We isolate exactly that valid finite implication and its converse, without asserting the later v_0 fork argument.

## Definitions

For a finite set P of old Q vertices, a complete prescribed old-to-future Boolean column `c : Nat → Fin d → Bool` (both directed edge bits of every future sort fixed consistently), and an arbitrary Boolean old graph E, define the raw age bound on every admissible support T by the previously checked source `Kk.finiteOldColumnRawBound`:

   B(T) = 3 - finiteDirectedCliqueCapacity E
                 (oldSupportCommonNeighbourPool P c T).

The common-neighbour pool is the subset of P adjacent to EVERY sort in T, not merely to some sort. The canonical finite integer graph age `G_B` is obtained from clique multiplicity witnesses respecting ALL supports, as in the project.

At the singleton support T={i}, the common-neighbour pool is exactly `P.filter (fun p=> c p i=true)`. The raw function B is SUPPORT-MONOTONE: if T⊆U then commonNeighbour(U)⊆commonNeighbour(T), clique capacity decreases, and consequently B(T)≤B(U). This is a genuine theorem for arbitrary E,P,c with finite support sizes; no global Henson extension density needed.

By the already checked `trackFCanonical_singleton_eq_raw` with the trivial singleton cap B(T)≤3, the canonical value at T agrees with B(T).

## The main equivalence

For ANY finite original-old pool P, ANY Boolean old graph E and ANY complete directed old-to-future column c, any nonempty future coordinate i : Fin d,

   G_B({i}) ≤ 2    ↔    ∃ p ∈ P, c p i = true.

Proof (⇒): Canonical singleton equals raw. If no old p has c p i=true, commonNeighbour({i})=∅, its clique capacity is zero, so B({i})=3. Contradiction.

Proof (⇐): If p is an old neighbour, the singleton {p} is a directed clique of size one (no pairwise-edge requirements), contained in the common-neighbour pool. Hence the clique capacity is at least one. Consequently B({i}) = 3-cap ≤2; canonical singleton equality gives G_B({i})≤2.

The result is exact for the finite **full old reference age**, not merely an abstract graph-age state whose value could have arisen from additional imposed external constraints. It is valid for d=1,2,3 and any d with an i. The graph E need not be symmetric for the capacity calculation; in Henson application the prescribed columns are BOTH directed bits and the old graph is K4-free.

## Hostile audit (16 checks)

1. Do NOT infer an old neighbour from an arbitrary graph-age function with F({i})≤2; one can stipulate a smaller abstract class without any old prefix. The finite-old-reference formula is essential.
2. The singleton canonicalizer agrees with raw B only because B is support-monotone; this must be proved, not assumed without checking.
3. The common-neighbour pool uses an intersection of full future type columns; for singleton i this reduces to one column.
4. An old neighbour exists in P, the ACTUAL specified old prefix; no demand that it belongs to a selected class or is a coding vertex.
5. Finite clique capacity≥1 follows from the one-vertex clique, regardless of whether E is symmetric/loop-free or whether the old graph itself has larger forbidden cliques.
6. The singleton support is admissible because ell=4 and i:Fin d; if d=0 there is no i and the assertion is vacuous.
7. Nat truncated subtraction matters: B=3-cap still satisfies B≤2 iff cap≥1, even for capacity≥4; no hidden K4-freeness assumption is needed for this algebraic equivalence.
8. The abstract monotonicity of raw capacity should be shown using antitone common neighbour pools and finiteDirectedCliqueCapacity_mono.
9. Full canonical witness constraints over ALL supports could in principle suppress singleton values for nonmonotone raw B. The verified singleton canonical equality explicitly rules this out here.
10. The exact old-to-future column c must be from the real Q construction before the omitted event when applying the result; an age computed over a different prefix cannot supply the required old v.
11. The one-old-neighbour theorem alone does NOT show that v_0 has positive L to the selected top and zero to the cap/auxiliary: that later claim still needs Q block nonedge geometry and H generation gate.
12. An old physical generation-zero coordinate v_0 is before the tested numeric cut only when v belongs to a base before the WHOLE omitted event. The manuscript argument explicitly uses such a v; verify this chronological premise when formalizing the application.
13. This theorem does NOT exclude a complete full Kpt I2 fork of two arbitrary meet/parameter nodes: the selected-vs-negative type case and every other I2 case remain.
14. No dependence on selected diary shadow equalities, source orbits, or any unproved BRD count appears.
15. Source modules `Kk/FiniteOldColumnAge.lean`, `Kk/LinkedCliqueCapacity.lean`, `Kk/TrackFSingletonCapacity.lean` are already merged with strict finite tests. The new theorem needs its own exact-head kernel compilation and named standard-only transitive axiom gate.
16. The manuscript currently marks `lem:small-independent-full-boring` PENDING; the resulting old-neighbour certificate is a verified COMPONENT only after a new gate passes, not authority to promote the whole lemma.

## Lean implementation

Create `Kk/K4SingletonOldNeighbour.lean` with:
- `finiteOldColumnRawBound_support_mono`: genuine support-monotonicity, using `oldSupportCommonNeighbourPool` antitonicity.
- `k4_canonical_singleton_le_two_iff_old_neighbour`: the equivalence above, via verified `trackFCanonical_singleton_eq_raw`.

A separate strict two-name `#print axioms` gate must build the exact module. If `simp` or arithmetic proof fails, repair the source proof first; do not insert sorry or custom axioms.

## Next application step

Instantiate `P` with the ACTUAL finite old Q prefix before the omitted meaningful event and `c` with its constant old-to-selected branch column. From the previously preserved singleton capacity at most two, extract v∈P with true old passing bit. Then prove by the actual numerical-H level formula that the generation-zero copy v_0 lies before the tested real cut and distinguishes the full dependent L+ records of the selected top from the negative auxiliary/cap source. This remains the concrete unsettled no-I2 bridge.

## Exact-head failed CI and English repair (16 November)

The FIRST dedicated workflow [43824932790](https://github.com/janhubicka/lean-kk/actions/runs/43824932790), tested at `968bc4ee97c242958b72e5c1ac30bd48aae30d07`, actually FAILED compiling `Kk.K4SingletonOldNeighbour`. Job log ID 133156394434 records:
- line 114: unknown constant `Finset.eq_empty_iff_forall_not_mem.mpr`;
- line 115: no goals left, owing to the invalid tactic combination;
- line 118: the proof of `B({i})=3` did not discharge the empty common-neighbour clique capacity goal; Lean reported `sorryAx` in the incomplete theorem.

The ordinary full `Lean` workflow at the same commit passed only because the NEW module was **not imported by the central `Kk.lean`**. That result must NOT be treated as verification of this particular theorem. Its separate source/gate is mandatory.

**Repaired English proof:** Establish the common-neighbour pool is empty by Finset extensionality. Membership in the filtered actual old pool gives one prohibited real old neighbour and contradicts `hNoOld`; the converse is impossible since the empty set has no members. Separately prove
`finiteDirectedCliqueCapacity E ∅ = 0` directly from the definition as a supremum over directed cliques: every subset of the empty pool is itself empty, hence every admissible clique candidate has cardinal zero. Only after that calculation may one rewrite `B({i})=3`. Thus no hidden assumption on E, no unsupported simplifier claim and no unproved axiom are introduced.

**Adversarial caveat:** the canonical singleton equation remains a component of the FULL actual old-column reference age, not of a freely stipulated selected age. Proving empty clique capacity is harmless general-purpose arithmetic and does not certify the remaining generation-zero full-Kpt fork argument. The repaired direct-module gate must check every named theorem, the strict standard-only axiom parser, and no `sorryAx`; its own exact-head success is required before merging.

## Second exact-head compile failure and source-only repair

The second direct job [43890191861](https://github.com/janhubicka/lean-kk/actions/runs/43890191861) at `1b09ee0c5135e5c050f46fcbe0d20cf7427d6d08` FAILED. Its actual Lean log, not guessed from the general workflow, shows:
- line 66: `Kk.finiteDirectedCliqueCapacity_empty` was **already declared** by an imported module (the helper's proposed name collided with an existing declaration);
- line 145: `No goals to be solved` after `rw [hEmpty, finiteDirectedCliqueCapacity_empty]`; this rewrite has already discharged the precise zero-capacity arithmetic identity, so the following `omega` was a dead tactic.
The incomplete theorem still reported `sorryAx`. The concurrent full Lean workflow again did not guarantee this standalone module compiled.

**Repair before the next gate:** Rename the local helper uniquely to `k4TrackD_empty_old_pool_clique_capacity`. Keep its independent explicit supremum proof for an actually EMPTY old pool (useful even though an imported theorem with a different name already exists). Change the rewrite to the renamed lemma and DELETE the redundant `omega` immediately after it. Keep the second `omega` outside the helper (where it actually concludes `¬(B({i})≤2)` from `B({i})=3`). Register the renamed helper in the strict script. The mathematical hypotheses and underlying full old-column canonical age remain unchanged.

No theorem may be promoted until the dedicated exact-head direct `lake build Kk.K4SingletonOldNeighbour` and strict named-axiom report BOTH pass, with no `sorryAx`.
