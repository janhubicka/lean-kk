# Track A/G — automatically construct a finite exact candidate Kpt index along an OLD AlgorithmRun

22 November 2026. English proof and adversarial audit FIRST.

## Problem and improvement

Track A/G's odd indexed structural budget assumes a single finite
candidate Kpt node universe with an exact live mask at every cut.
Earlier source-index theorems enumerate `closure(R.I(0),X)` for an
AlgorithmRun R with seed X. Our application compares the OLD actual
run R on X against the candidate larger seed Y, potentially with
X⊆Y but with NO actual AlgorithmRun on Y yet.

**Theorem.** Fix a genuine finite numerical-H+ model
`A=finiteNumericH K k N` avoiding normalized forbidden family
`family`, and seed sets X,Y in the same Kpt tree. Assume Y is a
subset of the *true* ambient represented prefix pool from finite
originals U⊆Fin N. Let R be an ACTUAL old AlgorithmRun on X,
with scan top T. No inclusion X⊆Y is necessary for this
indexing theorem.

Then there exists one finite Finset `params` of actual dependent
Kpt nodes and one mask
  live : Nat -> Fin params.card -> Bool
such that for every cut c<T and every actual Kpt node z,

  z ∈ closure(R.I(c+1), Y)
    iff exists j : Fin params.card,
      params.equivFin.symm(j).val = z AND live c j = true.

The index is injective and names the entire actual candidate FINAL
parameter closure `closure(R.I(0),Y)`, not merely the original
seed nodes. The Boolean mask at c is literal membership in the
actual pre-cut closure using OLD R.I(c+1), including all meets and
parameter-generated dependent auxiliary E nodes.

## Proof in English

1. Every seed y∈Y is below the genuine Kpt original of a finite
   numerical-H vertex v∈Fin N. Thus lev(y)≤freeLevel(v)≤v<N,
   so Y lies in the finite-level bound `levelLe N`.
2. The already checked successor-tree theorem
   `SMTree.Envelope.closure_finite_of_bounded` applies to
   the level set R.I(0) and seed set Y. This DOES NOT require
   that R is a run on Y. Hence
   Z=closure(R.I(0),Y) is finite.
3. Enumerate Z by `params=Z.toFinset`. Define `live c j`
   to be the decidable statement
   `params.equivFin.symm(j).val ∈ closure(R.I(c+1),Y)`.
4. The actual old AlgorithmRun satisfies
   `R.I(c+1) ⊆ R.I(0)` for c<T, by the previously verified
   final-tail description of descending selections. Monotonicity
   of parameter closure in the level set gives
   `closure(R.I(c+1),Y) ⊆ Z`.
5. Every z in that pre-cut closure therefore receives a unique
   index in params and its mask is true. Conversely any live
   indexed z is literally a member by its definition.

This is the true candidate source, NOT an assumed new run R_Y;
the index exists for any fixed larger or even unrelated Y that is
finite-model ambient-represented.

## Adversarial checks

1. R is a genuine AlgorithmRun only for OLD X. It is never
   silently reinterpreted as a run on Y.
2. The candidate index is from `closure(R.I(0),Y)`, NOT
   the old `closure(R.I(0),X)` (which may miss new nodes).
3. Ambient representation hY bounds levels of *every* candidate
   seed, even if Y is an infinite set of nodes as a type.
4. Parameter-generated and meet nodes are contained because
   the indexed set is the complete actual closure, not an
   enumeration of the finite original graph vertices.
5. Cut-level masks are exact for Y and the varying OLD R.I tail;
   no selected ordinary-L graph-age shadow enters.
6. The same finite params index is reused at all c<T,
   and both terminal nodes and noncrossing nodes are retained.
7. No-(I2) is not assumed: forked full crossing source nodes
   are all indexed, not collapsed into a partial function.
8. No `X⊆Y` assumption is mathematically necessary for this
   standalone finiteness statement, though later source
   transport theorems may require it.
9. No uniform bound on `params.card` independent of N or
   the finite original H carrier is proved; the promised diary
   bound on Q remains OPEN.
10. Finiteness does not establish any equality of old and
    candidate dependent Kpt ancestor profiles.
11. The theorem is about one fixed scan top and one old run.
    It does not compare two different scan heights or create
    a candidate Y AlgorithmRun.
12. This result removes the EXTRA exact-candidate-index
    existence hypothesis from the structural odd-Bad-budget
    setting once the two theorems are composed; it does not
    eliminate genuine odd Bad cuts or compute BRDs.
13. No frozen black manuscript changes or validation marks
    should be promoted until the exact-head Lean gate passes.

## Lean target

Standalone `Kk/TrackACandidateIndexOnOldRun.lean`, import
`Kk.NumericHExhaustiveRunIndex` and `Mathlib.Tactic`.
Reuse the verified finiteness proof and adapt the enumeration to
candidate Y while keeping the OLD R.I levels.
Direct module/full library build and strict named standard-only
transitive-axiom audit required.
