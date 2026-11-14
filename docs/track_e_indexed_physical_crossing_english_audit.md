# KK-free Track E (14 November 2026) — complete finite indexing of the *physical crossing relation*

**Starting point:** integrated `lean-kk` main `498b83ec77871b5efd9c38c7a75491cbc261f6c9`; prior Track E PRs #96/#107 merged and central 535-report gate documented. This note is the English proof and adversarial audit **before** writing `Kk/IndexedPhysicalCrossing.lean`. No claim of a common monoid orbit or an unconditional BRD bound is intended.

## E17. Intrinsic finite crossing relation, indexed by actual run-closure nodes

Fix a genuine normalized admissible Kpt tree, a physical finite numerical `H^+=finiteNumericH K k N`, a forbidden family avoided by its ordinary `L` reduct, an initial original pool `U⊆Fin N`, a seed set `X⊆ambientPrefixPool(H^+,U)`, and an actual AlgorithmRun `R` of horizon `top`.

Track C proves that the **complete final closure**
`Z_final = closure (admissibleKptSTree family) (R.I 0) X`
is finite and constructs one finite set `params` of its genuine Kpt nodes, the exact enumeration `node : Fin params.card → AdmissibleKptNode family` and the Boolean presence mask
`live(c,j) = true ↔ node(j)∈Z_c`,
where `Z_c=closure ... (R.I (c+1)) X`.

At cut `c` put
`Old(c,j) = kptFullOldAtCut (node j) c` and
`Upper(c,j) = kptFullUpperAtCut (node j) c`.
Both are `Option RawPartialTypeNode`, retaining **every** full `L^+` atom, including all incoming auxiliary `E` bits. They are `none` if `node j` does not cross the cut, even if `live(c,j)` is true.

Define the **finite-indexed physical crossing relation**
`IndexedCross(c,T,Q)` iff for some `j : Fin params.card`:

- `live(c,j) = true`;
- `Old(c,j) = some ⟨c,T⟩`;
- `Upper(c,j) = some ⟨c+1,Q⟩`.

### Exact theorem

For **every** `c<top`, including every genuine (I2) cut, `IndexedCross(c,-,-)` is **literally equal** to the intrinsic relation `FullPhysicalClosureCrossing family Z_c c` from merged Track E.

**Proof (forward).** Given an index `j`, live-mask exactness supplies an **actual** `z=node j∈Z_c`. A nonempty old option implies `c<lev z`; by Track C's exact Option/ancestor theorem, the two Option equalities identify the complete old and next raw ancestors of this SAME physical z as `⟨c,T⟩` and `⟨c+1,Q⟩`. Thus `(T,Q)` occurs in the intrinsic closure crossing relation.

**Proof (backward).** Given `(T,Q)` in that relation, choose its witness `z∈Z_c` of level >c. Track C's *exhaustive final closure index plus actual per-cut mask* supplies `j` naming precisely z and live at c. Apply its exact crossing Option/ancestor theorem. The two records are the required `some` values.

This theorem requires **no no-(I2) hypothesis**, no choice of a prescribed single-valued `F.target`, no chosen original-name representatives and no fake-source simplification. The index is physical, not merely an abstract finite collection of possible diary events.

## E18. Two different run indices and a finite *bisimulation* criterion

Let `P_1,P_2` index two (potentially different-sized) exact physical closure-node families, with live masks and old/upper functions. At one **aligned source cut c**, assume **two-sided coverage of indexed crossing pairs**:

- Every live, crossing index in the first trace has a live, crossing index in the second trace with precisely the SAME complete old/next `RawPartialTypeNode` values.
- Conversely every live, crossing index in the second trace is covered by one in the first with those exact values.

Then their finite-indexed crossing **sets** are equal. Combining with E17 for genuine numerical H+ AlgorithmRuns yields equality of the two intrinsic physical crossing relations at c. It does **not** require a bijection of all Kpt closure nodes or equality of the raw ambient H codes.

This is the precise hypothesis that can feed the already verified Track E `two_numericH_closures_B3_of_equal_full_crossing_relation` at no-(I2) cuts. In contrast, at a genuine (I2) cut the indexed relation can be multivalued: the same finite matching criterion still compares **all** crossing pairs without forcing a forbidden arbitrary choice of successor.

### Hostile cases and scope

1. **Present does not mean crossing.** A node z of level ≤c can be live but both Option ancestors are `none`; never add such a phantom edge.
2. **Pairs must come from one index.** Choosing old from j and upper from j' can invent a crossing never realized by any single Kpt node.
3. **All nodes, not selected originals.** An auxiliary meet/positive parameter may be in Z_c and witness a new pair even when the selected macrofront is unchanged; cuts 10/22 of the K4 run are mandatory regressions.
4. **Fake E predecessor bits count.** `RawPartialTypeNode` includes E; agreement of ordinary L reducts alone is not enough for E17/E18.
5. **No-(I2) must not sneak in.** At I2, a common old T can have two different upper Q's; the relation must retain both, whereas a `PrescribedBoringData` target function cannot represent both.
6. **Two-sidedness matters.** One-way matching only proves subset, not equality.
7. **Different finite multiplicities.** Two distinct Kpt nodes may give the SAME pair of ancestors; duplicate pairs are collapsed by a relation. Thus E18 suffices for the *crossing graph* and corrected-B3 comparison at no-(I2), but is NOT an isomorphism of full envelopes and does not by itself recover (I1)/(I2) incidence multiplicity.
8. **No canonical shared index.** `Finset.equivFin` is canonical only relative to one literal `params` finset; the selected numbers in separate runs need not agree. E18 avoids an unjustified bijection.
9. **No uniform diary bound.** `params.card` is finite for each *finite* numeric H run, but may grow with ambient N. This does not prove the required uniform finite number of diary types as N increases.
10. **Cut normalization required.** Raw `c` in separate target occurrences may differ by inserted boring gaps. E18 assumes common *source-coordinate* cut; an actual level normalization map and parameter transport remain open.
11. **Mismatched actual closures.** The theorem does not assume they coincide; it requires matching of their full indexed crossing pairs. Equality of selected F-ages or B3 truth values cannot replace this.
12. **Lower/upper source separation.** Corrected B3 is an ordinary-L age test, while the new physical crossing relation compares actual full L+ Kpt nodes; do not manufacture E for arbitrary L-witnesses.

## Exact pending integration contract

* Track C already provides the physical finite index and exact options. Track E formalizes the equality with the **canonical relation** for every cut.
* Track D/B must still classify which (I1)/(I2)/(I3)/(B3) **microevents** correspond between distinct occurrences; true (I2) cuts require remembering branching multiplicities/incidences not visible from the relation alone.
* To reach the common labelled source orbit, a synchronized source record must include all named dependent parameters, full selected-vertex inverse images, finite-event positions, source meets and genuine monoid transport. Equality of crossing relations alone is necessary comparison data but not sufficient to reconstruct the envelope.
* Unconditional `Lem:Kk_Diary_Determines_Envelope`, `Lem:Kk_Diary_Finite_Carrier`, and the successor-tree BRD upper bound remain PENDING.

**Validation gate:** direct module compilation and exact named standard-only `#print axioms` reports, plus full `lake build` on exact branch head, before recording any Lean certification. The shared `Kk.lean`, global validation scripts and frozen manuscript are not to be changed in this Track E PR.

## E19. Strong adversarial failure: crossing spectra cannot see terminal prefixes

There is a sharper reason why **even equality at every cut** of the complete old→upper crossing relations does not identify the whole source closure.

Suppose `x≤y` are genuine Kpt nodes, and an actual node set `Z` contains `y`. Adding `x` to `Z` changes **no** crossing relation at **any** cut:

`FullPhysicalClosureCrossing (insert x Z) c = FullPhysicalClosureCrossing Z c` for all c.

**Proof.** Only crossings witnessed by `x` could be new. If `c<lev x`, then `c<lev y`, and both the old ancestor of x at c and its next ancestor at c+1 are identical to the corresponding ancestors of y, because x is an initial segment of y. So the pair already has witness y∈Z. For c≥lev x, x never crosses the cut and adds no pair. Reverse inclusion is immediate. Every atom in the L+ pair, including E, is preserved by equality of the literal ancestors.

If also `x≠y` and `Z={y}`, then the node sets `insert x {y}` and `{y}` are different, even though **all** crossing spectra agree. This example is at the level of arbitrary actual Kpt NODE SETS; one must not claim it automatically constructs two different genuine AlgorithmRun closures without checking closure constraints.

**Why this matters.** An (I1) structural event detects the presence of an actual closure node *ending* at the event cut. The crossing relation tests nodes extending **strictly above** the cut and cannot see an extra terminal prefix when some longer node already supplies its shorter crossings. Thus E18's two-sided crossing-pair matching can certify equality of full B3 input graphs at no-I2 cuts, but **cannot by itself determine (I1) events, closure equality, labelled envelope isomorphism, or the common monoid orbit**. A suitable refined trace must additionally record terminal node membership, and enough node-incidence/meet data to identify (I2) multiplicities.

This is an explicit negative regression for the next Track E proof, not a proposed repair via increasing the upper-type spectrum: no spectrum-only strengthening will reconstruct the lost terminal membership. The per-cut live mask on the **actual finite Kpt node index** from Track C retains precisely the missing information, provided cross-occurrence indices are aligned by a genuine incidence-preserving correspondence rather than compared as sets of crossing pairs.

## E20. One physical finite index also recovers exact (I1) and (I2) structural tests

The terminal-prefix counterexample E19 shows that the crossing relation alone does **not** recover source presence or structural events. But Track C's exhaustive `params` index carries a separate *exact per-cut active-node mask*. The SAME named finite index recovers all three facts at once:

1. `(I1 at c)`: there is an actual `z∈Z_c` with `lev(z)=c` **if and only if** some index j has `present(c,j)=true` and `lev(node j)=c`.
2. `(I2 at c)`: there are actual `a,b∈Z_c` in one Kpt tree component with `lev(meet(a,b))=c` **if and only if** some pair of active indices i,j have the SAME component/meet property on their actual node values.
3. Complete full-`L^+` crossing relation: `IndexedCross(c)=Cross_{Z_c}(c)` as in E17, with no assumption on (I1) or (I2).

**English proof.** The exact coverage equivalence `z∈Z_c ↔ ∃j node(j)=z ∧ present(c,j)=true` transports every existential witness of (I1) and both witnesses of (I2), preserving their *literal actual Kpt values*. Conversely any active index represents a genuine closure node, so it witnesses the original source-level property. The crossing clause is E17. All three statements use **one fixed actual final-closure index for all cuts** in the same AlgorithmRun, so a parameter node that persists across multiple cuts retains the same name. No noncanonical meet decomposition or arbitrary selected-original name enters.

**Adversarial audit.** (i) Finite crossing pairs without the active-node mask cannot detect (I1), by E19. (ii) A record of only individual node levels and old/upper types, without access to the **actual meet relation** between named Kpt nodes, cannot certify (I2) incidence. (iii) One should not identify *different runs'* numeric index values: Track C's `Finset.equivFin` enumerates each actual final closure separately. (iv) The theorem classifies the geometric (I1)/(I2) tests exactly for a single genuine finite run but says **nothing yet** about the next selected event of the resolved unbounded diary or cross-occurrence normalization. (v) At no-(I1)/(I2), the full corrected (B3)/non-skippable (I3) analysis still depends on actual relative age and successor-tree lemmas, not on numerical source indexing alone. (vi) The index cardinality may grow with N and is not a uniformly bounded diary carrier.

**Lean targets:** `Kk/IndexedPhysicalStructuralEvents.lean` should export a purely logical exact-cover criterion for both structural event predicates, then a single actual finite numerical-H+ AlgorithmRun theorem combining that criterion with the verified C exhaustive index and E17 exact crossing equality. Both must receive direct exact-head compile and named standard-only axiom checks before validation.
