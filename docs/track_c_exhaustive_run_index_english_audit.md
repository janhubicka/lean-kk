# Track C — exhaustive finite index for the REAL numerical H+ AlgorithmRun closure
**13 November 2026; English proof and hostile audit before Lean.**
Baseline: main `888cbd8d7d68e7d1839cada300148f25d57b2b35`; Track C's former 14 endpoints are now **merged and globally registered** in the integrated 472-report build. This is a NEW independent branch from that main, not a continuation of the merged PR #99.

## The precise gap
Track E's `FullEventIndexedSourceRecord` requires a **common, exhaustive parameter-node domain** and a per-event active mask. The previous Track C final-pool result gives the same physical original name for each individual prescribed crossing, but does not itself enumerate *every Kpt closure node* at all cuts under a single parameter domain.

A noncanonical meet decomposition cannot serve as the source identifier: different pairs of full originals can have the same meet. The canonical referent is the **actual Kpt node**, not a recipe or an arbitrary witness pair.

## C10: finite final closure, uniformly over the whole run

Let `A=finiteNumericH K k N`, let `family` be avoided by `A.L`, let `U⊆Fin N` be an initial root pool, let `X⊆AdmissibleKptNode family` be the seed set with real prefix-pool representation
`X⊆ambientPrefixPool family A hAvoid U`, and let `R` be a genuine `AlgorithmRun` on X of height H.

Write `Z∞ = closure (admissibleKptSTree family) (R.I 0) X`.

**Claim.** The actual set `Z∞` is finite, even if X or the set of selected levels is supplied as a general Set rather than an explicit Finset.

**Proof.** Each seed z is below `A.kptOriginal v` for some `v:Fin N`. Hence
`lev z ≤ A.freeLevel v.val ≤ v.val < N`. This bounds X by the finite level-initial segment `Envelope.levelLe N`. The already kernel-checked successor-tree `closure_finite_of_bounded` states that the complete meet-and-parameter closure over **any** I stays inside that same finite level-initial segment. Hence Z∞ is finite. Crucially this is the actual `Kpt` closure, not an enumeration only of selected original vertices.

## C11: one exact Fin-index and a cut-by-cut live mask

Choose the full `Z∞` finset, and let `P = Fin |Z∞|`. The canonical within-run enumeration `node : P → AdmissibleKptNode family` obtained from that finset's `equivFin` is **injective and has range exactly Z∞**.

For each `p<H` define the TRUE pre-cut source
`Z_p=closure (admissibleKptSTree family) (R.I(p+1)) X`
and `present(p,j)=decide(node(j)∈Z_p)`.

**Claim.**
1. Every `Z_p` lies in Z∞, because the actual run-tail identity yields `R.I(p+1)⊆R.I 0` and closure is monotone in selected levels.
2. For **every** cut p, `present(p,j)=true ↔ node(j)∈Z_p`.
3. For every cut p<H and every actual closure node z, `z∈Z_p ↔ ∃ j:P, node(j)=z ∧ present(p,j)=true`.
4. If `present(p,j)=true` and `p<lev(node j)`, both old and upper raw Kpt ancestors are canonically defined:
`old=(ancestor(node j) p)`,
`upper=(ancestor(node j) (p+1))`.
Both are **complete dependent L+ types**, including E, unary and diagonal fields and negative atoms; neither is an abstract L-only age witness.

These indices enumerate all seed, meet and selected-parameter nodes, including intermediate auxiliary microlevels. No-(I2) is NOT assumed here; it is only needed to identify a *single-valued* canonical prescribed f_p from all crossings.

## C12: actual full-source record without choosing a meet recipe

The source-node index uses actual Kpt nodes themselves. Therefore if two normal-form recipes evaluate to the same closure node, their index is the same by injectivity. No uniqueness of meet decompositions is needed.

At a cut where no-(I2) holds, the earlier verified `finiteNumericH_run_final_pool_crossing_and_upper_types` provides `CoversClosureCrossing` and `IsCrossingGraphOf` for the full prescribed crossing F. The new exhaustive `present` index covers *every* underlying z witnessing those source and next-type records, so it supplies precisely the finite named parameter domain needed for Track E **within one run**.

The enumeration may use classical choice and is **not guaranteed to use the same numerical indices in two different runs**. A cross-occurrence comparison still needs literal source-node identities or an explicit bijection preserving the whole event-indexed record. In particular: an indexing theorem cannot prove a common labelled inverse-source orbit.

## C13: exact multi-root stage preservation (separate theorem)

Assume `X⊆ambientPrefixPool A U`. At an actual selected-level set I, put
`V=ambientStagePool A U I`, so
`closure I X ⊆ ambientPrefixPool A V`.
If the next seed set Y consists only of (a) actual nodes from this complete closure or (b) prefixes of newly inserted **genuine ambient originals** from a root set W, then
`Y⊆ambientPrefixPool A (V∪W)`.
This is proved by the real closure-in-originals theorem, monotonicity of `ambientPrefixPool`, and Set unions. It allows multiple old roots, meets, selected parameters and newly supplied physical roots **without** assuming each new seed is a single old root prefix.

This does NOT show that an arbitrarily stipulated resolved-copy schedule satisfies the premise on Y. Track B must still verify each inserted original and its exact L/E columns in the physical schedule. Nor does it bound |V| independently of N.

## Hostile checks
1. X may be a Set; finite closure follows from genuine bounded seed levels, not from finite X by fiat.
2. `lev(original v)` is its **canonical E free cut**, not its physical numeric position v. Use `freeLevel v ≤ v`.
3. The output P indexes complete **Kpt nodes**, not original names. The old `Fin V.card` pool indexes original witnesses and is a DIFFERENT finite domain.
4. Repeated meet recipes must collapse to the same node. Do not assert a unique pair of originals.
5. All pre-cut closures use the SAME AlgorithmRun and X. Moving to a different run invalidates the index.
6. The live mask is true exactly at actual closure membership; do not use a selected-shadow or ordinary L age.
7. A node can be present but not cross the cut (its level can be ≤p); distinguish `present` from `crosses`.
8. Old/upper ancestors are only asserted when p<lev node, and the upper is at p+1, not p.
9. Fake numeric H coordinates can appear as E predecessors in a full partial type, although a positive-free-level TARGET is real; no fake information is erased from the indexed Kpt node.
10. No-(I2) is irrelevant for raw indexed closure but essential for identifying a single assigned next type of a prescribed source T.
11. This index is finite *per run*, not a uniform bound on source size nor a canonical cross-occurrence index.
12. The new-root transition assumes genuine originals in A and a valid seed-coverage statement; no magic construction of a new Henson stage.
13. K4 cuts 10/22 still need their full auxiliary microevents; a finite index does not render them boring.
14. Do not claim final BRD numbers, corrected B3, or common labelled source orbit.

Lean module targets: `Kk/NumericHExhaustiveRunIndex.lean` and `Kk/NumericHMultiRootPreservation.lean`. First prove and strict-audit the finite/run index and per-cut mask; then discharge the multi-root transition without modifying any protected manuscript prose.
