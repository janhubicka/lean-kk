# Track E E78 — exact equivalence: physical stage-original OLD prefix matching ⇔ complete candidate Kpt old-socle coverage

**20 November 2026. English mathematical proof and adversarial audit committed BEFORE Lean.**

## Adversarial correction to E74

Merged E74 proved that matching the COMPLETE OLD Kpt ancestor of each *active stage original* with one physical OLD-LIVE source suffices to cover the OLD Kpt ancestor of EVERY candidate NEW-LIVE crossing source node, including generated meets and dependent parameters.

Its accompanying English audit explicitly declined NECESSITY, suggesting a node might have an old match while an unrelated representing original does not. This was overly cautious **for the predicate as actually defined**: the condition is imposed only on original v that represent SOME actual new-live crossing z, and **every such representative has exactly the same c-level Kpt ancestor as z**. Thus if z has an OLD-LIVE matching ancestor, O_v has the same witness. An original that represents no crossing z is *not active* and carries no test.

This note repairs that incorrect caveat and proves that the two physical source-exact predicates are EQUIVALENT. It does not assert that the geometric predicates hold for the resolved diary.

## Actual setting

Fix family of normalized forbidden complete dependent L+/E partial Kpt types, actual finite numerical-H+ A=finiteNumericH(K,k,N) avoiding family, an actual physical original root-name pool U⊆Fin N, a true OLD AlgorithmRun R on X, and a seed family Y⊆ambientPrefixPool(family,A,hAvoid,U) for the candidate new source. At one physical source cut c use the SAME genuine OLD selected-level tail J=R.I(c+1) in both closures:

    Zold=closure_J(X),     Znew=closure_J(Y).

No new AlgorithmRun on Y is assumed; X⊆Y is NOT needed just for the local equivalence. It is used elsewhere for whole-run transfer.

Define **SourceSocle(c)**:

    For each z∈Znew with c<lev(z), there is
    w∈Zold with c<lev(w) and
    ancestor_c(z)=ancestor_c(w)

as equality of ACTUAL full Kpt ancestor nodes, including all directed E and negative ordinary L atoms.

Define **ActiveOriginalPrefix(c)**:

    For every v∈hStageOriginals(K,k,N,U,J), IF
       there exists z∈Znew with c<lev(z) and z≤O_v,
    THEN there exists w∈Zold crossing c with
       ancestor_c(O_v)=ancestor_c(w).

Crucial: O_v itself need not belong to Znew, and a stage original not representing any new crossing node is VACUOUS. Equality refers to literal Kpt nodes, not selected-front L-reducts or just the underlying original graph.

## Theorem E78 — exact iff

    SourceSocle(c)  ⇔  ActiveOriginalPrefix(c).

### (⇐): already Lean-verified in E74

Fix any z∈Znew crossing c. The true source normal-form/stage-pool theorem selects v∈hStageOriginals with z≤O_v. Therefore v is active. Apply ActiveOriginalPrefix to obtain a genuinely OLD-LIVE w with ancestor_c(O_v)=ancestor_c(w). Since z≤O_v and c<lev(z), level-tree uniqueness gives ancestor_c(z)=ancestor_c(O_v), hence the desired SourceSocle witness.

This is the already verified E74 `finiteNumericH_candidate_old_socle_of_active_original_prefixes` theorem, under the exact physical source representation Y⊆ambientPrefixPool.

### (⇒): missing reverse, now explicit and elementary

Fix an ACTIVE original v with a witness z∈Znew crossing c and z≤O_v. From SourceSocle applied to this *particular z*, take OLD-LIVE w crossing c with ancestor_c(z)=ancestor_c(w).

Monotonicity of LevelTree height under z≤O_v gives c<lev(O_v). By level-tree uniqueness (verified `LevelTree.eq_ancestor_of_le`):

    ancestor_c(z) = ancestor_c(O_v).

Compose its reverse with the witnessed source equality:

    ancestor_c(O_v) = ancestor_c(z) = ancestor_c(w).

Thus the same genuinely OLD-LIVE source w witnesses ActiveOriginalPrefix for v. Stage membership is needed only to identify which originals the predicate tests; no injective index, canonical representing original, or new-run existence is used.

This reverse implication actually works for arbitrary source sets once the "active representative" premise z≤O_v is provided; the finite numerical-H+ stage representation is required only in the forward direction.

## Consequences and limits

1. The E74 physical original-prefix certificate is NOT an accidental overapproximation of new-source **old-socle** coverage. It is an exact reformulation, involving at most N physical original names in each finite stage, regardless of the number of generated Kpt meet/parameter nodes.
2. At zero ordinary-L candidate stages with symmetric whole ambient L, E72 upgrades this exact old-socle coverage to inclusion of COMPLETE old/upper dependent L+/E crossings (all I2 forks). The reverse from paired crossings to old-socle coverage is plausible but is NOT asserted here; it would require independently proving that every live crossing contributes the corresponding full pair with an old witness.
3. E73 plus E76 then yield full no-novelty at a genuinely old-boring one bare-root positive even-real cut if the whole eligible original zero-L column and the active original-prefix coverage conditions hold. This remains CONDITIONAL on both geometric predicates.
4. The K4 auxiliary E/q2 cuts 10 and 22 are not treated as inherently boring. No global bounds uniform in diary size, inter-occurrence source coordinate alignment, common labelled inverse-source monoid orbit or BRD upper/sharp theorem follows.

## Hostile checks (20)

1. SourceSocle quantifies over the COMPLETE physical candidate closure, including meets and dependent parameters.
2. Both old/new closures use exactly J=R.I(c+1) of ONE old run, not independently chosen tails.
3. Y⊆actual ambient original-prefix pool is needed for E74's forward implication.
4. X⊆Y is unnecessary to prove this local logical equivalence.
5. Every new source node has SOME true stage original representative, but that representative need not be unique.
6. Every active original represents SOME genuinely NEW-LIVE crossing z; mere presence in the stage pool does not make it active.
7. An original not representing a crossing new source creates no test and cannot be a counterexample.
8. An original representing multiple z has the SAME ancestor at c for all crossing z≤O_v.
9. A source z can have multiple representing originals; all of them have the SAME c ancestor when crossing.
10. The representative original O_v need NOT itself belong to Znew or Zold.
11. The old witness w MUST be an actual OLD-LIVE crossing Kpt source node, not a graph-age type.
12. Old Kpt ancestor equality includes E and negative ordinary L bits, not just positive L.
13. Height monotonicity z≤O_v is used to show c<lev(O_v).
14. LevelTree.eq_ancestor_of_le gives literal ancestor equality, avoiding guessed type restrictions.
15. No I2 fork uniqueness or functional upper-type mapping is assumed.
16. The reverse implication does not require finite numerical-H+ original-stage coverage; only the stipulated active representative witness.
17. The forward implication does require actual full stage representation, verified in Track D/E74.
18. One test per original yields a bound by N, NOT a diary-uniform bound.
19. Terminal I1 and actual upper-type matching are separate logical conditions outside this pure old-socle iff.
20. Real K4 auxiliary microcuts, cross-occurrence normalization, labelled monoid source orbit and BRD remain open.

## Lean gate and manuscript discipline

Create an independent module importing merged E74, whose theorem statement is an exact two-way source-socle/original-prefix iff for genuine numerical-H+ candidate closures, no new run. Reuse the existing verified E74 direction verbatim and prove only the reverse via `LevelTree.eq_ancestor_of_le`. Register one qualified `#print axioms` check, dedicated direct Lake build and strict parser negative self-test, and independent full CI. Patch the mistaken E74 English-audit assertion ("not necessary") in a separate targeted audit update; do not alter the verified E74 Lean theorem or protected black manuscript. No validation promotion before both exact-head gates pass.
