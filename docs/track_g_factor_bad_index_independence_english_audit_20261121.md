# Track G — intrinsic exact factor Bad support, independent of finite target names

21 November 2026. English proof and adversarial audit BEFORE Lean.

## Existing verified inputs

- G398: exact same-I/same-total-F run transport iff the unique old boring factor extends to every new crossing and no new I1/I2 obstruction occurs.
- G406: for independently EXACT finite target Kpt index, the finite old-factor Bad Finset is empty iff there exists a synchronized actual target run. G406 merged at 01dcf80472796ad460b3a05f779564acba7781a3 after dedicated and full Lean CI.
- G378: any represented finite numerical-H+ target Kpt seed pool and any selected level tails nested in I(0) admit an exhaustive *complete* finite Kpt source index without a target run.

## Theorem A: physical one-cut compatibility iff indexed compatibility

Let C be the actual complete target Kpt source at a cut c. Define a PHYSICAL predicate by three conditions: (T) every z∈C has level ≠c; (M) no pair z,w∈C lies in the same successor-tree component with meet level c; (F) every genuine total monoid D with RX.F(c)=RX.F(c+1)∘D sends the lower ancestor z|c to upper ancestor z|(c+1) for every crossing z∈C.

Let `node:Fin Q→Kpt`, `live:Nat→Fin Q→Bool` be exact: z∈C iff some j has node(j)=z and live(c,j)=true. Then `KptIndexedOldFactorCompatibleAt` is equivalent to the physical predicate. Proof each way: exactness preserves terminal witnesses, pair witnesses and every actual crossing factor equation. No injectivity, index bijection, source cardinality equality, or a target run is needed. The F equality is a TOTAL MMap equation, not a finite-set restriction.

## Theorem B: exact canonical factor Bad set is independent of indexing

If two target name systems (possibly with different cardinalities and duplicates) are both exact at EVERY cut c<top for the complete candidate source closure(S,RX.I(c+1),Y), then they yield identical `kptExactOldFactorBadCuts` Finsets. For each cut, apply Theorem A to both indices. Its old-boring condition depends only on RX, and membership reduces to failure of the same physical compatibility predicate. Extensionality gives Finset equality, not merely equivalent zero sets.

## Theorem C: finite numerical-H+ physical stage needs no target index assumption

For one actual old RX on X⊆Y with both seeds contained in the same finite numerical-H+ prefix, the already verified G378 target-index construction applied to I=RX.I gives a target Finset of full Kpt source nodes and true live masks for all pre-cut tails. The required nesting RX.I(c+1)⊆RX.I(0) follows from genuine `RX.I_eq_final_tail_of_run`. Apply G406 to obtain existence of this exact target index together with the equivalence `its exact factor Bad Finset is empty iff some genuine RY exists with RY.I=RX.I and RY.F=RX.F`.

## Adversarial checks

1. Index exactness enumerates the WHOLE dependent meet/parameter Kpt closure on RX.I tails, not selected graph vertices.
2. Only one old actual AlgorithmRun is assumed; the target run is a conclusion.
3. The physical compatibility predicate is defined at an arbitrary cut; its old-F factor quantifier could be vacuous at an interesting cut, but the canonical Bad support filters ONLY genuine old-boring cuts.
4. At an old-boring cut RX.noninteresting_step supplies the unique genuine old total factor by G309 left cancellation, so the actual geometric compatibility test is non-vacuous.
5. No requirement of injective node index or equal P,Q. Indexed duplicates are harmless.
6. Actual same-component I2 meets and I1 terminals remain separate from the complete crossing equations.
7. Total monoid F equality is used, not equality of selected ordinary graph ages.
8. All crossing Kpt ancestors retain dependent auxiliary E and negative ordinary L.
9. At a true new terminal at c, the crossing law cannot detect it; terminal absence is independent.
10. Source inclusion X⊆Y is required for the G406 transport equivalence, not for physical-vs-indexed one-cut equivalence.
11. Index-independence of a finite Bad support does not show a uniform number of bad cuts as the physical stage grows.
12. A classical Finset and universal quantification over total monoid maps is not an executable finite algorithm.
13. K4 genuine selected auxiliary cuts 10 and 22 are not silently reclassified as boring.
14. Equality of local profiles can forget physical source identity (verified G366); no labelled inverse source or orbit follows.
15. No chronological diary cut reindexing, resolved unbounded numerical-H+ copy, corrected (B3) continuation or sharp BRD theorem is asserted.

## Lean acceptance

Prove physical/indexed one-cut equivalence, the equality of exact Bad Finsets for independent exhaustive target indices, and the constructed finite-H+ exact-Bad transport equivalence. Dedicated exact-head Lake build, three source-qualified standard-only #print axioms reports, strict parser negative self-test and independent full build. No frozen black manuscript changes.