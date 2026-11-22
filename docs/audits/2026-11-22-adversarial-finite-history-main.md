# Adversarial whole-project checkpoint and Track B finite stage-history repair
22 November 2026 — English proof and hostile audit BEFORE new Lean source.

## Audit method and scope (not a blanket verification claim)

Current repository: 679 Lean files, with 315 direct imports in \`Kk.lean\`.
The central exact \`#print axioms\` registry has 1,017 DISTINCT reported names,
each paired with a qualified \`#check\`; the gate parser rejects custom
transitive axioms and \`sorryAx\`. A successful build verifies only those
concrete declarations and imported dependencies. No conclusion about the
unregistered modules, mathematical adequacy of the statements, or the global
diary classification follows by counting reports.

The manuscript has 353 tracked validation markers, including 27 genuinely
PENDING. The remaining claims include: bounded resolved copy in H+,
the prescribed sorted cover/split/code history, full parameter-closed
Kpt (I1–I3)/corrected-B3 transfer, labelled inverse-source orbit, all
diary occurrences, lower/upper equality, and Lean validation of the
finite I3 recurrence. A previous estimate "92%" is NOT a mathematical
confidence level or a proven fraction of the final theorem.

The high-risk boundary checked in detail here is:
\`Kk/PhysicalCanonicalCoverStage.lean\`
  -> \`Kk/TwoPhysicalCanonicalCovers.lean\`
  -> \`Kk/FinitePhysicalCoverChain.lean\`
  -> manuscript bounded resolved-copy and covering claims.
The single-stage theorem gives a GENUINE physical reserved clique,
literal gap-inclusive columns and one finite universal top witness.
The two-stage theorem gives separate top witnesses. The recent finite
chain theorem verifies terminal canonical age and initial column
preservation, but its *public statement discards stage certificates*.
That weaker result is correct; it must not be used as a certificate
of a coherent prescribed diary.

## New theorem: entire finite chain as an inductive certificate

Fix the *same actual graph* E, ell>=2, d>0, a prescribed age list A(i),
support T(i), clique-block sizes r(i), and heights k(i). Let
PhysicalCoverHistory(i,n,b,c,F,cFinal) be the least predicate such that:

* for n=0, F=b and cFinal=c;
* for n+1, there exist an actual clique Q of size r(i), a genuine
  cutoff b'≥b containing Q, and the complete column
  c'=supportBlockGappedColumn(b,Q,T(i),c), with all original gaps
  explicitly zero;
* Q is anticomplete to the ENTIRE earlier original prefix, in both
  directed orientations, c' keeps c on all p<b, and canonical age
  over [0,b') is the prescribed A(i+1);
* the same stage has an ACTUAL \`HasUniformPositiveSupportStage\`
  certificate for its complete normalized finite future;
* the remaining n-stage certificate starts from precisely
  (b',c') at index i+1.

**Existence.** If every A(i+1) is an actual cover of A(i), with
A(i,T(i))=A(i+1,T(i))+1 and ell=A(i+1,T(i))+r(i)+1,
and the initial physical complete column has age A(0), then
there exist F,cFinal and PhysicalCoverHistory(0,steps,b,c,F,cFinal).

**English proof.** Generalize to starting index i and remaining length n
with i+n≤steps, and maintain current canonical age A(i).
Induct on n. Base n=0 uses the identity history.
For n+1, i<steps. Genuine-cover positivity and the maximum bound
A(i,T)≤ell−1 imply r(i)>0. Apply the existing Lean-verified complete
one-stage Henson theorem. Obtain Q, b', size, chronology, actual
clique/anticompleteness, canonical age A(i+1), and one stage-local
numerical-H witness. Define c' to be the literal gapped column.
Because every q∈Q satisfies q≥b, c'=c on every p<b. Apply the
induction hypothesis to i+1,n,b',c' with its DERIVED initial age.
Build the stage-history constructor with the exact witnesses.
There is no additional existential coherence assumption.

A companion structural induction on this history yields final age
A(i+n), monotone final cutoff, and preservation of ALL columns from
the starting prefix. The existence theorem is strictly stronger
as a *typed certificate* than the former final-age-only theorem,
but does not add a new combinatorial density assumption.

## Independent adversarial checks

1. The prescribed finite cover chain is an INPUT, not proved from a
   diary or produced by the physical theorem.
2. Every A(i) comes from genuine \`AgeCover\` objects; arbitrary
   pointwise decreasing functions are not accepted.
3. The unit drop and the block-size identity are BOTH necessary inputs.
4. The derived positivity r(i)>0 is essential: without it one cannot
   find a reserved q to show b≤b'.
5. Every Q is a TRUE original clique, not a formal subset of a
   hypothetical extension graph.
6. Each Q is anticomplete to the complete preceding original prefix,
   not just previously selected names.
7. The intervening enumerated original gaps remain in the old pool.
8. Their complete column is zero, but their actual internal graph
   edges are unchanged; we never delete or re-enumerate them.
9. The complete previously established columns remain byte-for-byte
   unchanged on EVERY p<b at the next step, including old reserved
   blocks.
10. A physical raw age may change at ALL subsets of T; only the
    canonical cover conclusion is used.
11. No false equality between raw numeric bounds and canonical age
    is asserted.
12. The proof uses one unchanged E and one same fixed d. It does not
    handle splits or deletion of sorts without the separately verified
    canonical sort pullback.
13. Each stage has its own finite numerical-H witness; the history
    constructor does NOT equate successive maps f or cutoffs M.
14. Earlier top future witnesses are NOT protected by the old-column
    clause unless their ACTUAL images have been incorporated into the
    complete prefix and their positive columns certified neutral.
15. No source-coordinate monotonicity or chronology of target
    embeddings is inferred merely from original cut b≤b'.
16. No claims about dependent Kpt auxiliary E, full L+/E,
    corrected B3, I1/I2/I3, selected source masks, or monoid orbits.
17. The finite cover-chain history can contain extra actual
    parameter-closed interesting cuts; it does not count them.
18. The result is finite for every prescribed n, not a single
    countably coherent tower. Passing to n→∞ needs compatible choices.
19. Henson freeness and OnePointLeftDense remain explicitly assumed;
    the proof does not derive the latter from the unlabelled age alone.
20. Full future stage feasibility is checked by the preexisting
    one-stage theorem, not by a fresh informal gluing argument.

## Remaining genuinely new obligation after this repair

A **selected-witness preservation / neutral-extension** theorem.
Given a finite stage certificate and a finite set of ACTUAL images
of its chosen top witnesses, find an extension of the original
cutoff that retains their complete *possibly positive* typed
columns while keeping the entire canonical age and full parameter-
closed Kpt event record unchanged. Existing zero-gap insertion
only preserves ages with columns set to zero and does not establish
this. The anchored positive-neutral lemma needs a genuine clique
capacity witness for each prescribed active support.

Until that lemma and the Kpt orbit comparison are proved, this
finite history cannot be promoted to the bounded resolved copy,
characterization, 24-orbit theorem, or exact big Ramsey degrees.



## Cross-track source-to-manuscript audit matrix

The whole proof was audited by following the **critical inter-track interfaces**
and their actual theorem signatures, rather than treating the number of
Lean files as a metric for a completed proof. The root has 315 distinct direct
imports and the 1,017 central axiom reports are distinct and paired with
`#check`; this does not imply every one of the 679 `.lean` files has
an axiom-checked public theorem or that all unregistered code was audited.

| Track | Checked theorem/signature | Adversarial scope boundary |
| --- | --- | --- |
| A | `PartialNumericForbiddenSharpStability`, `PartialNumericCriticalGenerations`, `PartialNumericSingletonCanonical` | Fixed actual original graph and given later top names; changes in ORDINARY binary-L canonical age, not full dependent Kpt event history |
| B | `FinitePhysicalCoverChain`, `PhysicalProspectiveControlledCoding`, `PhysicalCanonicalCoverStage`, `HensonLeftDensityBridge` | Fixed Henson E; full literal old columns retained; finite stage top witnesses are separate; selected witness survival/neutrality and global scheduling are not conclusions |
| C | `TrackCUnifiedSafeRealOdd`, `TrackCRawOriginalOldSocle` | Full OLD Kpt-prefix matching is required at maximal eligible safe cuts; the verified implication does NOT construct those matches in an unbounded resolved diary |
| D | `TrackDZeroStageActualRunSkip`, `TrackDTopSeedConcreteLowerSkip` | Actual no-I1/I2/I3 finite skips have explicit no-seed, complete zero-stage/Plan roles or top-seed shape; cannot globally erase positive auxiliary (B3) microcuts |
| E | `TrackEOldSocleOriginalMaxFrontier`, `TrackESelectedLevelOriginalBudget` | Number of original-prefix tests is bounded by roots plus ACTUAL selected old levels, not by a fixed diary: both the old selected-level count and existence of prefix witnesses remain open |
| F | `TrackFK4CompleteTupleSynchronization`, `TrackFZeroCodeSurvivorSynchronization`, `TrackFZeroCodePreprofileRigidity` | Complete finite graph classes are synchronized under genuine rank-large target sourceCodingFibre hypotheses; no end-to-end realization of every specified cover/split/code history in every induced Henson self-copy |
| G | `TrackGExactFactorBadCuts`, `TrackGIntrinsicExactFactorBad`, `TrackGZeroStageExactBadTrichotomy`, `TrackGBadCutCoordinateTransport` | Bad=empty iff one same-I/same-total-F target run exists under exact finite index; conditional coordinate/source transport DOES NOT build a common labelled inverse-source orbit or bound exceptional cuts uniformly |

### Specific audited hazards

1. **The left-dense enumeration is a separate, strong hypothesis.**
   `OnePointLeftDense E ell` requires the realizing original to be
   nonadjacent to *all intervening earlier indices*, not merely to
   satisfy an extension property over a specified finite prefix.
   This is faithful to the manuscript's explicitly chosen left-dense
   enumeration, but the theorem has not constructed such an enumeration
   from a generic countable Henson presentation. In particular one
   must not silently replace `OnePointLeftDense` with K_ell-freeness
   or ordinary age-universality.
2. **An exact finite source index is not a labelled source orbit.**
   The indexed-Bad criterion takes a complete list of genuinely live
   target Kpt nodes; different indices may represent the same node.
   `Bad=∅` gives a *single* synchronized run, not a canonical
   cross-occurrence identification of the nodes in all diaries.
3. **The K4 parameter-cut counterexample is real.** The numerical-H
   gadget selects an extra auxiliary cut while the selected graph-age
   shadow stays constant. Therefore any proposed induction that
   counts only selected-front age covers and treats all other levels
   as boring needs a new dependent-source proof. A bounded list of
   abstract cover operations cannot by itself eliminate I2/B3.
4. **Source-rank largeness is a hypothesis, not blanket diary
   unavoidability.** The fully verified Track F tuple theorem assumes
   all source coding fibres have rank-large compatible target fibres.
   That condition is not derived for all synchronized complete
   histories. In the manuscript, the longer frozen black induction
   is not the Lean proof; the olive TODO correctly flags the difference.
5. **The manuscript numerical recurrence is not the lower-bound proof.**
   The small K4 independent-triple recurrence has a `leanpending`
   marker, and the uploaded diary generator omits 5,904 of the
   120,487 proposed abstract histories. Even if the recurrence is
   independently confirmed arithmetically, one must prove that every
   counted history is *realizable and unavoidable* under the intended
   normalization, and that the generated diaries and chosen orbit
   equivalence agree.
6. **A verified conditional implication cannot be promoted by using
   its conclusion as an invariant.** Repeatedly: the full-stage
   zero-L or old-socle premise in Tracks C/D/E, and the complete
   source-class equality in Track F, need independently constructed
   witnesses for the selected resolved diary.

### Recommendation for the critical path

Priority 1 is a real **selected-witness-preserving extension**:
simultaneously protect a finite set of actual earlier top-witness images,
keep their possibly nonzero future columns, preserve all normalized
clique support ages, and obtain the exact full parameter-closed Kpt
source event comparison. Only THEN attempt a coherent infinite tower.

Priority 2 is the direct independent-set diary occurrence theorem
built from the verified source/target tuple equality and full coding
step; independent-set degree counts should remain conditional until
this is completed.

Priority 3 is an explicit proof in Lean that the manuscript's
left-dense, Fraisse and coding-tree enumeration interfaces match the
Boolean hypotheses used by the physical constructors.

**Do not interpret 1017/1019 checked theorems or 353 validation
markers as a percentage of the final main theorem.** 142 green,
175 conditional blue, six finite, three successor, and 27 pending
is a useful bookkeeping census, not a measure of the complexity
or completeness of the global proof.
