# Track A/G — automatically indexed odd Kpt Bad-cut budget from one old run

22 November 2026. English-first proof, including a redundancy audit.

## Verified inputs, no duplicated indexing theorem

The current main already contains the verified Track E theorem
`finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index`
in `Kk/TrackECandidateSourceFiniteIndex.lean`. It constructs a
finite exact candidate parameter-closure index, for candidate seed
Y, at the actual pre-cut selected-level sets R.I(c+1) of ONE OLD
AlgorithmRun R on X. Crucially there is no AlgorithmRun on Y.

It ALSO contains the independently exact-head verified merged
Track A/G theorem
`finiteNumericH_odd_bad_card_le_structural_plus_missing`
from PR #484, which assumes an exact finite candidate index and
bounds exact old-factor Bad odd cut coordinates by Q+Q² plus
the number of odd candidate-source cuts missing OLD full Kpt
lower ancestors.

An attempted standalone duplicate of E70 was discovered by CI
as a Lean symbol conflict and closed unmerged (PR #491).
We REUSE E70 instead; never copy the proof or add competing names.

## New theorem, removes the index-existence hypothesis

Fix the original finite numerical-H+ graph-signature model
`finiteNumericH K k N`, an actual family avoidance proof,
its genuinely symmetric binary L, the finite real-prefix original
set U⊆Fin N, two Kpt seed sets X⊆Y, and Y contained in the
actual ambient represented original pool.

Let R be an ACTUAL old AlgorithmRun on X at scan top top.

Then there exist ONE actual finite source-node set `params`
and Boolean live mask `live : Nat -> Fin params.card -> Bool`
such that:
1. for every cut c<top, live indexes EXACTLY the full true
   candidate pre-cut closure `closure(R.I(c+1),Y)`,
   including meets, parameters, E and negative L;
2. writing Q=params.card and node(j)=params.equivFin.symm(j).val,
   the actual old-factor Bad ODD cut set satisfies

   |BadOdd(node,live)| <= Q + Q² + |MissingOldSocleOdd(node,live)|.

In particular, the right-hand side is a theorem about the
EXISTING actual finite numerical-H source, not a free additional
index assumption or a hypothetical Y-run.

### Proof

Apply the independently verified E70 candidate index theorem
to `family, K,k,N,hAvoid,(U:Set(Fin N)),X,Y,hY,top,R`.
It supplies params, live, and exact coverage at every cut.
The first part of the desired conclusion is exactly that coverage.
Apply the merged #484 odd-Bad cardinal theorem with Q=params.card,
node from params.equivFin, and these same live masks.
The cardinal bound follows directly without any new model
construction.

## Strengthened zero-missing-old-socle specialization

Suppose additionally that for every actual ODD cut c<top and
every crossing z in the candidate closure, the old closure at
the same pre-cut selected levels contains a crossing w with
the SAME complete OLD Kpt ancestor. Then the constructed
MissingOldSocleOdd set is empty, so
  |BadOdd| <= Q + Q².
This remains conditional on a genuine parameter-closed
old-socle matching property, NOT on merely equal ordinary-L
raw ages. No construction of the target Y-run is concluded.

## Adversarial checks

1. The index is constructed for Y along OLD R.I, not for
   closure of a guessed new AlgorithmRun on Y.
2. The verified E70 source covers all generated Kpt meet and
   E parameter nodes, not just finite selected original names.
3. Q=params.card is finite but is NOT proven bounded independently
   of numeric carrier N or height; no uniform BRD conclusion.
4. The old level sets are actual R.I(c+1), and old-vs-candidate
   comparison is at the same c; no height reindexing.
5. Only candidate Y requires the ambient-representation
   hypothesis for indexing; the odd-Bad theorem also requires
   X⊆Y and the full actual L symmetry.
6. The finite index may be injective here, but #484's bound
   does not depend on that additional property.
7. The exact Bad predicate is the OLD factor compatibility
   test; do not conflate it with the residual `D` set of
   mismatching full profiles between TWO independently
   constructed AlgorithmRuns.
8. Missing-old-socle cuts overestimate truly Bad cuts.
9. Odd zero ordinary-L bits alone do not remove I1 terminals,
   I2 meets or missing complete old ancestor witnesses.
10. E70 was already formalized and compiled before this PR;
    avoid duplicate theorem declarations (PR #491 closed).
11. The zero-missing corollary requires old prefix matching on
    ALL relevant candidate crossings, not simply on one shadow
    or original column.
12. No inverse labelled source orbit or global BRD theorem
    follows, and no frozen black manuscript or validation marks
    should change before exact-head Lean verification.

## Acceptance

New `Kk/TrackAOddAutomaticIndexBudget.lean` importing
`Kk.TrackECandidateSourceFiniteIndex` and
`Kk.TrackAOddIndexedStructuralBudget`.
Standalone strict named axiom gate + direct and full `lake build`.
The source should remain draft until those gates pass.
