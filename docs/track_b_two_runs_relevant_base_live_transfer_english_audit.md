# Track B — two REAL Henson runs: finite old base-pair support and live cut-star matching
**14 November 2026. English mathematical proof committed before Lean, STACKED on PR #198.**

## Critical-path combination

Parent [Track B PR #198](https://github.com/janhubicka/lean-kk/pull/198) aims to prove that a **finite** set of base-graph pairs completely determines all OLD ordinary-L atoms of the numerical-H construction through a literal source cut c. A relevant pair i<j has allowed real copy generations q,m≤k with q<m or q=m=k, and BOTH `hPosition k i q` and `hPosition k j m` ≤c. If two base graphs agree in both directed bits on this finite set and have the same generation k, their complete old ordinary-L socles coincide at any common physical cut, without requiring global equality of E.

Merged [Track B PR #193](https://github.com/janhubicka/lean-kk/pull/193), verified with 656 standard-only reports, constructs REAL finite Henson AlgorithmRuns with possibly different physical base graphs, seeds, entire meet/parameter closures and finite live Kpt indexes. Full corrected-B3 comparison still takes as a premise `SameInitialL P.occurrence.ambient.L Q.occurrence.ambient.L c`; the present stack DISCHARGES it from the explicit finite geometric base-pair condition.

## Four endpoints

### A. Old ordinary-L prefix agreement from finite real base pairs, for TWO actual runs

Take `P,Q : HensonPhysicalRunCutData ell hell c`, not arbitrary selected subpools. Assume `P.k=Q.k` and, for every `HensonRelevantBasePair P.k c i j`, equal directed source base bits
`P.E i j=Q.E i j` and `P.E j i=Q.E j i`.

Their genuine Henson forbidden-family certificates supply physical irreflexivity, so the diagonal atoms agree automatically. Each physical finite ambient contains c. Invoke the checked generic occurrence adapter from PR #198 to deduce:
```
SameInitialL P.occurrence.ambient.L Q.occurrence.ambient.L c.
```
No assumption `P.E=Q.E`, no invented source-rank transport, no Kpt source identity and no equality of auxiliary E or chosen selected-front age F.

### B. Complete full corrected-(B3) equivalence from finite local base agreement plus intrinsic spectra

If additionally
```
∀ R, PhysicalCutStarUpperL family P.occurrence.Z c R ↔
     PhysicalCutStarUpperL family Q.occurrence.Z c R
```
then the checked PR #193 actual-run theorem applies with A's derived old socle. Therefore
`P.occurrence.fullProfile.CorrectedB3 family ↔ Q.occurrence.fullProfile.CorrectedB3 family`.

The real AlgorithmRuns derive exact FULL name-set equality and exhaustive final original-pool coverage independently, not postulated; positive-cut upper-L type equality remains an explicit geometric premise.

### C. A direct live Kpt-node matching certificate for B3, with NO abstract old-socle premise

Suppose both P and Q have **EXACT** actual live Kpt-node index presentations `nodeP,liveP` and `nodeQ,liveQ`: for each complete upper ordinary-L type R, the respective `IndexedPhysicalCutStarUpperL` predicate agrees with the intrinsic physical `PhysicalCutStarUpperL` of the actual source. Such true finite indexes are independently constructed for both runs by the already verified `numericH_actual_run_all_cuts_indexed_cutStar`.

If `IndexedCutStarLiveCover Pidx Qidx c` and the reverse cover hold, the previously checked bilateral source-name cover equivalence yields matching projected cut-star spectra. Use the two exact index projections and Theorem B. Hence the whole local full corrected-(B3) verdict agrees. No identification of OLD dependent `L^+`, auxiliary E records or Kpt node cardinalities is required.

### D. Full corrected-B3 disagreement forces a missing actual physical cut-star type

Under the same finite local base-pair assumptions, if P full corrected B3 FAILS and Q passes, the generic verified physical Henson cut-star theorem gives an actual physically cut-adjacent full original v in P with complete next ordinary-L reduct R **absent** from Q's allowed upper cut-star profile. Source exhaustiveness in both true runs identifies their permitted star profiles exactly with their intrinsic physical positive-cut upper-L spectra. Thus
```
∃R, PhysicalCutStarUpperL family P.occurrence.Z c R
    ∧ ¬ PhysicalCutStarUpperL family Q.occurrence.Z c R.
```
This is the base-independent, source-exact missing physical cut-type obstruction. The stronger true LIVE Kpt-node counterpart follows from PR #193 when the actual finite indexes are constructed; no fake next-type or arbitrary B3-witness E is inserted.

## Adversarial checks (15)

1. The relevant base-pair set is exact physical generation geometry; it is NOT merely the selected graph-age support mask.
2. Both directed bits must match, since the generic numerical H copies ordered binary atoms in both directions.
3. Same generation parameter k remains essential; different k can produce different permitted real-copy gates even on identical base E.
4. Both actual finite H sources contain the same literal source cut c; comparison of different target gap positions requires a separate reindexing.
5. The finite local base agreement need not imply global E equality: arbitrary higher/unrelated base pairs may differ.
6. Diagonal/loop atoms agree because each base Henson model is explicitly loop-free; not silently omitted.
7. Both full-source exact name selection and parameter/meet closure original-prefix exhaustion are DERIVED from genuine AlgorithmRuns, not their old one-sided `hRepresented` field.
8. The actual source uses `Run.I(c+1)`; maintained final original source pool uses `Run.I 0`.
9. The full no-(I2) certificate is required for each corrected-B3 prescribed source function; physical live index relations may exist even with I2.
10. The ordinary-L positive-cut flag is not an E edge; fake E-positive coordinates are not countable matches.
11. The live cover matches COMPLETE next ordinary-L reducts, preserving all absent directed atoms, unary and diagonal data, not just the single positive cut edge.
12. The projected spectrum equality and bilateral live matching are remaining independent geometric inputs, not automatically derived from the proposed canonical diary F.
13. No upper-upper L edges in an arbitrary B3 continuation witness are copied from the physical ambient source.
14. The K4 auxiliary q2 positive-cut type remains part of the genuine source, even if the selected x-only graph-age has a passing B3 profile.
15. Full I1/I2 E-dependent event records, source-coordinate rank synchronization, relative continuation/B3-loss, common labelled inverse-source orbit, and exact big Ramsey upper/lower bounds remain OPEN.

## Verification gate

English FIRST; implement four named endpoints in `Kk/B3TwoRunsRelevantBaseTransfer.lean`. Parent #198 must first pass exact-head **661** standard-only reports on its integrated main. This stack then targets **665** reports, complete `lake build` and parser self-test; update for concurrent merges. Do not modify frozen black manuscript text or mark the global theorem green.
