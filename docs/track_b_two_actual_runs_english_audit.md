# Track B — two actual finite AlgorithmRuns: projected indexed cut-star controls corrected B3
**14 November 2026. English mathematical proof and hostile audit committed BEFORE Lean.**

## New interface, not a new geometric assumption hidden behind a name

Track B's merged PR #154 (606 strict standard-only reports) now proves:
- from a **genuine** finite numerical-Henson `AlgorithmRun` at a no-(I2) cut c, construct an actual `HensonCutOccurrence` whose Full name set is **exactly** the closure-selected originals, and whose maintained final original-name pool represents every Kpt closure parameter and meet at the pre-cut source;
- its complete prescribed OLD/UPPER `L^+` crossing graph is exactly the choice-free physical closure crossing relation and its allowed upper ordinary-L cut-star spectrum is exactly the intrinsic positive-cut projection;
- for two such finite Henson occurrences built from the **same literal base E and generation k**, their complete old ordinary-L prefixes agree at any common c, even with different truncation sizes N;
- for each true finite run, one finite **actual Kpt-node** index with exact per-cut live masks computes that intrinsic physical cut-star spectrum for all scan cuts, including physical (I2) forks at the relation level.

The next lemma combines these existing proofs **without leaving source exhaustiveness or old socle alignment as external hypotheses** for two genuine runs.

## Common-base run data (a genuine physical source type)

Fix once:
`ell≥2`, a numerical generation parameter `k` with `ell≤k+1`, a single symmetric loop-free K_ell-free base graph `E:Nat→Nat→Bool`, and a common source cut c.

Define a `HensonRunCutData` record whose fields are: finite carrier bound N, actual finite seed pool `U : Finset (Fin N)`, genuine finite numerical-H avoidance `hAvoid`, Kpt seed nodes `X`, exact original-prefix seed representation `hX : X⊆ambientPrefixPool ... U`, actual algorithm `Run : AlgorithmRun ... X top`, and the real bounds `c<N`, `c<top` and full no-competing-(I2) on its `Z=closure ... (Run.I(c+1)) X`. The underlying E,k,ell and their graph/family certificates are SHARED by the two records, while N,U,X,top,Run and the physical Kpt closures can differ.

Use the checked `actualHensonRunCutOccurrence` (not a generic `HensonCutOccurrence` with fake Full) to define `P.occurrence`. Its `Full` is definitionally the exact closureSelectedOriginal predicate for the actual maintained finite original-name pool.

## Theorem A — actual-run full-source completeness is automatic

For any `P : HensonRunCutData`, the checked `actualHensonRunCutOccurrence_fullExact` and `...poolExhaustive` provide both:
`∀ v, P.occurrence.Full v ↔ closureSelectedOriginal ... v`
and
`∀ z∈P.occurrence.Z, ∃v, z≤P.occurrence.ambient.kptOriginal ... v`.

No separate abstract Full/exhaustive pool assumption survives. Since each seed is actually a prefix of an original in U, the proof covers every parameter/meet produced by the full AlgorithmRun closure. The two CutData records do not share a Kpt source or any arbitrary original name.

## Theorem B — full B3 agreement for two genuine runs over ONE base, conditional only on intrinsic cut-star projection

Let `P,Q : HensonRunCutData` share the literal E,k and source cut c by their dependent type. Assume ONLY:
```
∀ R:RelationalPrefixType(c+1) 1 0 1,
  PhysicalCutStarUpperL family P.occurrence.Z c R ↔
  PhysicalCutStarUpperL family Q.occurrence.Z c R.
```
The preceding theorem supplies exact source completeness for each run; the previously verified `HensonCutOccurrence.same_base_old_socle` discharges old ordinary-L socle alignment **because E and k are SHARED**. Now apply the verified cross-ambient full-B3 transfer theorem to conclude:
```
P.occurrence.fullProfile.CorrectedB3 family ↔
Q.occurrence.fullProfile.CorrectedB3 family.
```
This is a genuine finite **two-run** theorem, not a re-labelled abstract source lemma. It shows the ONLY external B3-comparison predicate required in this common-base, common-source-cut setting is equality of the intrinsic physical positive-cut complete upper-L spectra. It DOES NOT assert that a selected diary determines these spectra.

## Theorem C — an actual finite indexed Kpt-node comparison suffices for two runs

For each P, the verified `numericH_actual_run_all_cuts_indexed_cutStar` returns a genuine finite set of FULL final closure Kpt nodes `paramsP` and live Boolean mask `presentP` such that for all c<top,
```
IndexedPhysicalCutStarUpperL family (fun j=>(paramsP.equivFin.symm j).val)
  presentP c R
  ↔ PhysicalCutStarUpperL family P.Z c R.
```
Apply separately to P,Q to obtain **two** finite (possibly different cardinal) index universes, each with its actual live mask and full-source coverage. If their projected indexed cut-star predicates agree at the common c for every complete upper ordinary-L type R, use the two projection equalities to establish the intrinsic equality assumed in Theorem B. Conclude equality of the **full corrected-(B3) tests for the true runs**.

The result can be stated as the *existence of these two genuine finite indexes* together with the conditional implication:
```
(∀R, IndexedPhysicalCutStarUpperL P_idx c R
       ↔ IndexedPhysicalCutStarUpperL Q_idx c R)
  → P.fullB3 ↔ Q.fullB3.
```
Because the indexes are constructed from the actual closure, this is not an invented arbitrary matching certificate. No size bound depending only on the diary is inferred; the full Kpt index cardinal may grow with N.

## Hostile audit checklist

1. Source c is COMMON and literal, not merely two different target numerical gap indices.
2. Same base E and same generation k are explicit SHARED type parameters; an arbitrary diary occurrence does not automatically satisfy these without an embedding/normalization argument.
3. Physical Henson K_ell freedom, loop-freeness and symmetry are explicit, not extracted from selected graph-age F.
4. Each X genuinely lies under finite original-prefix pool U, not just an unrelated Kpt seed set.
5. Each real source `Z` is the FULL pre-cut `Run.I(c+1)` meet/parameter closure; final `Run.I 0` is used ONLY to index maintained originals.
6. The full no-(I2) hypothesis applies separately to P and Q and cannot be replaced by absence of visible selected-front meets.
7. BOTH full-name equality and original-pool exhaustiveness are derived from actual AlgorithmRuns; a one-sided abstract `hRepresented` is insufficient.
8. The source-name carrier `Fin V.card` comes from maintained original names, while Track E's finite **Kpt-node** index enumerates all final closure nodes. Those two finite indexes are NOT the same.
9. The complete `L^+` crossing contains auxiliary E and false atoms. Its positive-cut projection retains complete next ordinary-L types only AFTER actual sources are verified.
10. The physical indexed cut-star is well-defined even at I2; the B3 chosen partial source needs no-(I2), so the theorem explicitly uses it for its two runs.
11. The upper–upper edges in an arbitrary corrected B3 witness are freely chosen; none are equated to ambient E or to the numeric-H graph.
12. The true cut-star may contain K4 q2 auxiliary originals omitted from selected macro-F; the theorem compares the FULL projected sources.
13. Equality of projected cut-star spectra is **assumed**, not proved from a diary. This remains the core cross-occurrence geometric invariant to construct.
14. No claim that the two complete Kpt source relations or parameter/meet spans have a common labelled inverse monoid orbit.
15. No relative fixed-source continuation/B3-loss equivalence follows from local B3 truth-value equivalence.
16. No uniform bound on size of the actual Kpt-node index based only on a finite macrodiary, no unconditional big Ramsey degree formula or independent lower bound.
17. This proof is a finite, true-run comparison; no countable infinite resolved-copy schedule is constructed.
18. Black manuscript text and global TODOs are frozen; only a scoped BLUE interface may be added after full exact-head Lean CI.

## Verification gate

Commit English-first proof BEFORE Lean; propose three named endpoints in `Kk/B3TwoActualRuns.lean`: actual-run source completeness, two-real-run corrected B3 iff of intrinsic physical spectra, and existence of two actual finite live indexes whose projected equality implies full B3 agreement. Current merged central baseline is **606** strict reports at [run 43599761313](https://github.com/janhubicka/lean-kk/actions/runs/43599761313), so this branch targets **609 exact named standard-only reports**, full `lake build`, parser self-test and final tested/merged tree equality. No manuscript-global green mark pending.


## Review against newer merged Track E/A/D modules (14 November, later checkpoint)

The proof above is still distinct from `ActualRunNumericHPrefixStability`, whose two actual runs share the literal Kpt seed set X and whose selected-level sets agree automatically. Here two runs may have DIFFERENT genuine seed sets, finite original pools, pre-cut closures, final Kpt-node indexes and Henson truncation heights. The only common physical data are the base E, generation k and source-cut coordinate c. No equality of selected-level sets is assumed or proved.

`ActualRunLevelProfileSync` has a separate stronger stagewise FULL L+ crossing relation/terminal-I1 hypothesis to synchronize selected levels; our projected positive-cut L spectrum is weaker and suffices only for the local corrected-B3 verdict.

The newer Track D actual-run bad-core iff is compatible: it describes a local finite forbidden clique core once source completeness is known. We do not infer the common bad core from a common diary, or equate upper-upper arbitrary continuation edges to E.

**Merge discipline:** source branch `kk-track-b-two-real-runs-indexed-cutstar-20261114` contains this English proof only; create a fresh branch from the latest shared main, commit this audit BEFORE Lean, and keep all independently merged A/C/D/E/F/G imports and axiom reports intact. Check exact current central report count, which may exceed the older 606 baseline.
