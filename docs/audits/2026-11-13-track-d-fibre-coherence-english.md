# Track D continuation: fibre-coherent cut-neighbour criterion (English first)
13 November 2026

## Theorem A (geometric criterion implying marked → full corrected B3)

Fix `ell ≥ 2`, `k` with `ell ≤ k+1`, a symmetric, loop-free, K_ell-free base edge table E, genuine finite numerical `A=H(E,k,N)`, `C=A.L`, tested `cut<N`, a fixed finite original-name family `original : Fin M → Fin N`, and selection predicates `Full`, `Marked`.

Let `G=selectedStagePoolPrescribedData A cut original Marked`. Suppose:

1. **An actual eligible marked source exists:** `∃ v, Marked v ∧ cut+1 ≤ A.freeLevel(original v)`.
2. **Cut-neighbour coverage, not whole-pool inclusion:** each `Full`-selected **eligible** v with `C.binary cut (original v) 0 = true` is `Marked`.
3. **Fibre-coherent complete L output:** whenever `Marked v, Marked w` are both eligible and have equal complete old L+ source `A.partialTypeAt cut (original v)=A.partialTypeAt cut (original w)`, their *complete next ordinary L-reducts* coincide at `cut+1`. This is weaker than equality of next auxiliary E records but stronger than equality of positive cut edges.
4. **G passes corrected B3** for the genuine normalized Henson family.

Then the `Full` selected-stage pool also passes corrected B3.

### Proof (no hidden choice of representative)

By (1), G.source is nonempty, using the specific eligible marked name. For any Full-selected eligible v adjacent to cut, (2) makes v marked. Let `T=A.partialTypeAt cut (original v)`. Then T belongs to G.source, witnessed by v. The *chosen* G.target(T) comes from SOME eligible marked representative w of T, by the verified `selectedStagePoolPrescribedData_source_original`. It need not choose v! But (3) ensures that this actual target's complete ordinary next L-reduct equals v's `(cut+1)` L-type, irrespective of the choice. Thus all premises of the previously hosted-verified cut-visible transfer theorem `henson_fullB3_of_cut_visible_complete_outputs` hold. Apply it with (4).

This theorem does not demand `Full ⊆ Marked` or compare E on a hypothetical L-only continuation. Conversely it does not assert that fibre coherence holds in the proposed globally resolved Kpt source.

## Theorem B (cut-visible B3 equivalence on one literal H)

For two finite selections U,V of the SAME fixed literal H, assume each selected-stage source is nonempty. Assume each cut-eligible, cut-adjacent U-name has its complete (cut+1) L-reduct among the actual chosen V outputs, and reciprocally. Then U.CorrectedB3 iff V.CorrectedB3. Apply the cut-visible transfer in the two orientations. No equality of all original names, E types, old source sets or **off-cut** complete upper spectra is required.

This equivalence is confined to TWO selections in ONE ordinary-L socle. To compare two unrelated ambient H copies, additionally construct a literal same-initial-L identification; do not silently reuse it.

## Adversarial tests / false implications

- A selected v itself need not be the chosen representative of its old source T. Without (3), target choice can lose v's complete L-reduct even when v belongs to both pools.
- The source set may be empty if every marked name is ineligible; then its B3 test is vacuous. Hypothesis (1) cannot be replaced by mere `∃ Marked v`.
- Testing only `L(cut,original v)` is not enough to determine v's entire `(cut+1)` L-type. Fibre coherence retains all positive **and negative**, both directed, diagonal and unary atoms.
- Off-cut Full-selected originals may have extra types. They cannot appear in a forbidden clique *created at cut*, because the checked small-clique-core theorem puts cut in every forbidden clique and requires each upper vertex's complete crossing type.
- Upper--upper future L-edges remain freely selectable in an arbitrary B3 continuation; the proof never imports them from real H.
- The concrete K4 cut-10 q2/x microevent refutes replacing condition (2) or the cut-visible complete-type coverage by the selected x-shadow.
- No direct original-diaries B3 equivalence, physical full Kpt E-source identification, graph-age fidelity, or labelled inverse orbit is inferred. Keep the global manuscript claims pending.

## Validation discipline

The preceding English proof/audit is deliberately committed before the new Lean declarations. Compile the exact module with the pinned dependency, register each new declaration's strict named transitive-axiom report, and confirm full-project integration before assigning any theorem-level mark. The manuscript may discuss these conditional results in olive text only. Black text and its old TODOs stay byte-identical.
