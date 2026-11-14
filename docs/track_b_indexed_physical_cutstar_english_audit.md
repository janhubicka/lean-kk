# KK-free Track B — finite indexed certificate for the INTRINSIC physical cut-star
**14 November 2026. English proof before Lean, with adversarial checks.**

## Context and improvement

Merged Track B PR #141 proves that when a claimed FULL selected original pool is certified exhaustive, the complete corrected-(B3) cut-star spectrum is the intrinsic positive-cut ordinary-L projection `PhysicalCutStarUpperL family Z c` of the actual choice-free `FullPhysicalClosureCrossing family Z c`.

Track E has already proved a much stronger finite **physical source-index** theorem: for any actual numerical-H AlgorithmRun, a single finite set of ALL final Kpt nodes and an EXACT per-cut Boolean `presentAt` mask encode the entire complete OLD/UPPER `L^+` crossing relation at every actual cut `c<top`, including I2 forks. The stronger full indexed *pair* relation has far more data than is needed for corrected (B3).

We now define a **finite indexed cut-star projection**, retaining just the **complete next ordinary-L reducts with actual positive cut edge**. This gives an explicit, independent-of-original-name certificate for exactly the part of an event-indexed source relevant to local B3.

## Definition

For an arbitrary finite normalized Kpt family in the graph signature, an index type Params of actual Kpt nodes `node : Params → AdmissibleKptNode family`, a per-cut Boolean live mask `presentAt : Nat → Params → Bool`, and a source coordinate `c`, define:

```
IndexedPhysicalCutStarUpperL family node presentAt c R :↔
  ∃ (T : PartialTypeWithE c 1 0 1)
    (U : PartialTypeWithE (c+1) 1 0 1),
      (T,U) ∈ IndexedPhysicalCrossing family node presentAt c
      ∧ U.lReduct = R
      ∧ R.binary (some (Fin.last c)) none 0 = true.
```

The `IndexedPhysicalCrossing` membership is **itself** a concrete witness by one actual live index j with:
`presentAt c j = true`,
`kptFullOldAtCut (node j) c = some (c,T)`, and
`kptFullUpperAtCut (node j) c = some (c+1,U)`.

Neither a noncanonical seed/parameter/meet recipe nor a selected graph-age F is substituted for the REAL active Kpt node. The same index supplies both old and upper L+ records.

## Theorem A — a finite LIVE source name for every indexed cut-star type

Unpack the definition: if `IndexedPhysicalCutStarUpperL ... R`, extract a **real index j** with live Boolean = true, and a source/upper complete type pair T,U whose exact Kpt old and upper ancestor values are recorded at j. Require also U.lReduct=R and the positive ordinary-L cut bit. This makes the abstract set-membership predicate a concrete finite check and prevents arbitrary future–future edges from being confused with the physical cut edge.

## Theorem B — exactness under a genuine exhaustive active index

Suppose `hExact : ∀ z, z∈Z ↔ ∃ j, node j=z ∧ presentAt c j=true`. Track E already proved
`IndexedPhysicalCrossing ... c = FullPhysicalClosureCrossing family Z c`.
Therefore simply substitute this equality under the *same* existential projection and obtain:
```
∀ R,
  IndexedPhysicalCutStarUpperL family node presentAt c R
  ↔ PhysicalCutStarUpperL family Z c R.
```
The result holds even when I2 forks exist: the physical relation and its projection are well-defined before choosing a partial source-to-target function. B3 equivalence only later invokes no-(I2) to use a prescribed function.

## Theorem C — actual finite numerical-H AlgorithmRun index for EVERY cut

Take a true finite numerical-H AlgorithmRun with seed `X⊆ambientPrefixPool ... U`, and top scan height `top`. The verified Track E
`numericH_actual_run_all_cuts_indexed_physical_crossing`
constructs ONE finite Kpt node universe `params` covering the entire final closure and an exact live mask `presentAt` at **every** scanned cut. Take its exact physical crossing equality for cut c<top, apply theorem B (or direct relation rewriting), and conclude:
```
∃ params, presentAt,
  (∀ z, z∈params ↔ z∈finalClosure)
  ∧ ∀ c<top, ∀ R,
    IndexedPhysicalCutStarUpperL family
       (fun j : Fin params.card => (params.equivFin.symm j).val)
       presentAt c R
    ↔ PhysicalCutStarUpperL family
       (closure ... (Run.I(c+1)) X) c R.
```
**No no-(I2) hypothesis** is needed to compute this projection; it becomes relevant only for the corrected-(B3) partial-function interpretation. This is a real finite stage source representation, not an invented diary event index.

## Theorem D — across occurrences only the projected finite trace needs matching for B3

For two actual closures Z1,Z2 at a common source cut, each with its own (possibly different-size) index and exact live mask, suppose the two indexed cut-star *projected* predicates agree for every complete upper-L type R. Applying theorem B separately to the two closures gives equality of their intrinsic physical cut-star spectra. This is strictly **weaker** than Track E's earlier assumption matching every full OLD+UPPER L+ pair of physical crossings; it permits variation of off-cut sources and auxiliary E atoms. It still does not assert either old socle alignment or that the proposed diary implies the projected equality.

When coupled to the already kernel-checked Track B PR #141 exhaustive physical occurrence and an independent old-socle alignment, this finite indexed projection is a sufficient B3 transfer input. It does NOT establish common labelled source orbits.

## Adversarial checks

1. The projection retains the full upper ordinary-L reduct through c+1, not only a single positive cut edge.
2. The required cut edge is an **ordinary L** bit, never auxiliary E.
3. A Boolean live index j alone is insufficient: j must cross c and have BOTH `some` old and upper Kpt ancestor records.
4. The old and upper records must belong to the SAME actual Kpt node j.
5. The equivalence to a true closure requires exact two-sided active index coverage; a one-sided indexed subpool is not sufficient.
6. I2 forks may be present: the physical crossing RELATION and its cut-star projection still make sense. A prescribed B3 FUNCTION is not assumed there.
7. Empty cut-star spectra are allowed and produce no fake anchor or default upper type.
8. The Kpt source index includes generated meets and parameters, not just original seed or selected graph-age vertices.
9. The physical trace can contain false L and auxiliary E facts; the projection forgets E only AFTER the true physical source is identified.
10. Upper–upper relations of an arbitrary B3 continuation remain free and are not transported.
11. A fixed actual run has one finite full source-node universe, but there is no uniform bound on its size from an unrefined diary.
12. No source-coordinate rank transport is assumed; cross-occurrence theorem compares equal c.
13. The equality of two indexed projected spectra is NOT inferred from selected macrodiary F equality.
14. Old ordinary-L socle alignment is a separate cross-occurrence hypothesis, unless the two runs use the same base E and k (Track B same-base lemma in separate draft).
15. Complete I1/I2 event labels and E record matching remain necessary for full labelled inverse-source orbit.
16. The K4 q2/x microevent remains a regression: q2 is a true full source if it contributes an active positive physical cut type.
17. No unconditional exact big Ramsey degree, lower bound or full refined-diary realization follows.
18. Black manuscript text remains protected; add only a conditional blue interface after an exact-head full Lean build and standard-only axiom audit.

## Strict gate

Implement four named endpoints in `Kk/B3IndexedPhysicalCutStar.lean` with central imports and axiom registry. Latest main used for this branch is `3a1cc085aecce7fd2896d82e7624040b2d056500`; the exact central report baseline must be confirmed, likely 547 after PR #141 source certification. Full exact-head `lake build`, parser self-test and four additional strict named standard-only transitive-axiom reports required; no green global manuscript marker.
