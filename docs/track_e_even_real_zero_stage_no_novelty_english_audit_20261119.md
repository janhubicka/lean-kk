# Track E E73 — complete no-novelty at positive even-real zero stages

**19 November 2026. English argument FIRST, adversarially audited before Lean.**

## Context

Track E E72 (source PR #392) proves that in a genuine finite numerical-H+ pre-cut stage, zero ordinary L bits on ALL eligible stage originals plus actual OLD FULL Kpt socle coverage force COMPLETE OLD/UPPER dependent L+/E physical crossing inclusion, with all I2 forks. The theorem is local and still assumes a separate no-new-I1-terminal statement.

Track D PR #389 is now independently Lean-verified and merged. It proves that at a **positive even real** H+ position c=hPosition(k,idx,g), with no actual initial seed ending at c, symmetric ambient ordinary L and zero ordinary L(c,v) for EVERY eligible original in the TRUE stage original pool, the entire parameter-closed Kpt closure has no terminal I1 at c. This uses the real closure normal form, oddness of positive E free levels and the full dependent original-meet obstruction, not an invalid assumption that all closure nodes are selected originals.

E73 composes these results in the **candidate source computed from the old run's I(c+1)**, yielding a complete no-novelty certificate at the cut without assuming a new run, a new source index, an I2-free closure or any terminal predicate as an extra hypothesis.

## Statement

Fix `family : List (NormalizedForbidden 1 0 1)`, a finite numerical-H+ structure A=finiteNumericH(K,k,N) avoiding family, symmetric ordinary L in A, original-pool U⊆Fin N, actual nested Kpt seeds X⊆Y⊆ambientPrefixPool(family,A,U), and ONE old genuine Kpt AlgorithmRun R on X. At a positive even real source cut c=hPosition(k,idx,g), define

    Zold = closure_(R.I(c+1))(X),
    Znew = closure_(R.I(c+1))(Y).

Assume:
1. **No true initial Y seed ends at c:** no y∈Y with lev(y)=c.
2. **Whole-stage zero original column:** for every v∈hStageOriginals(K,k,N,U,R.I(c+1)) whose genuine free E-level exceeds c, A.L.binary(c,v,0)=false.
3. **Old full-Kpt socle coverage:** for each actual z∈Znew crossing c, some actual w∈Zold crossing c has the SAME COMPLETE old Kpt ancestor at c.

Then `NewRootNoNoveltyAtCut family Zold Znew c` holds.

Proof. The StageFinset original predicate equals the actual ambientStagePool original predicate; this is checked by expanding their definitions, with no appeal to the final original pool. Apply Track D's exact even-real no-full-I1 theorem with seed set **Y** and stage level set **R.I(c+1)**. The positive even coordinate and zero-stage hypotheses exclude every new terminal, including terminal meets and dependent parameters. Apply E72 to the same Y,X and R.I(c+1): exact socle coverage plus the zero column force the same complete old/upper L+/E crossing relation in the required NEW→OLD direction. Combine these two conclusions into `NewRootNoNoveltyAtCut`.

**Graph specialization.** When A is built from `normalizedGraphModel E` with E symmetric, checked Track D `finiteNumericH_graph_ordinary_L_symmetric` supplies the complete ambient ordinary-L symmetry (including odd fake coordinates). Crucially the auxiliary E remains directed.

## Geometric significance and limits

The main remaining condition for omitted positive even real levels becomes an old FULL-Kpt socle representation test, not the full next L+/E pair condition or independent new-I1 analysis. The cut may still fail the socle coverage hypothesis! This is not a proof that all base-graph omitted levels are boring. The K4 auxiliary cut 10 and 22 pattern is retained: this theorem applies there only if ALL its genuine hypotheses are actually established. A separate proof for nonzero ordinary-L columns, auxiliary odd/fake cuts and true selected levels remains necessary. No diary-uniform exceptional bound, labelled inverse-source orbit or BRD conclusion is claimed.

## Hostile audit (17)

1. Exactly ONE actual old AlgorithmRun; new source uses its I(c+1).
2. Seed set Y is genuinely represented in one finite numerical-H+ ambient original-prefix pool.
3. The ambient ordinary L symmetry is across all numerical positions; auxiliary E need not be symmetric.
4. The tested c is an actual even real H+ address, not an arbitrary source coordinate.
5. c>0 is required; the root c=0 is excluded.
6. No initial seed in **Y**, not merely in X, ends at c.
7. Zero bits cover ALL eligible true stage originals, including auxiliary generators.
8. Stage is `R.I(c+1)`, not `R.I(0)`.
9. A physical original may represent a source node but need not be an actual source node itself.
10. Actual parameter closure can produce meets not appearing as initial seeds; Track D normal form handles them.
11. The old complete Kpt socle, not only ordinary graph L prefix, is matched.
12. E72 turns zero ordinary L plus full old Kpt ancestor equality into complete L+/E upper ancestor equality.
13. At I2 forks each source pair is transported separately; no single-valued prescribed map assumption.
14. The result is a local true no-novelty certificate, NOT automatic boringness at all source cuts.
15. K4 auxiliary E/q2 cuts 10 and 22 are not declared boring by fiat.
16. No global resolved stage Plan induction or cross-occurrence Kpt source normalization is asserted.
17. No finite diary carrier, monoid orbit or sharp independent-triple BRD follows.

## Formalization

Lean module imports exact merged Track D even-real terminal and Track E E72 zero-column crossing. Prove the genuine StageFinset→ambientStagePool zero predicate adapter, actual cut-level no-novelty theorem, and graph-specialized symmetry version. Dedicated named standard-only axioms and independent full build; do not promote manuscript marks until exact-head success. Preserve black TeX and old TODO decisions.
