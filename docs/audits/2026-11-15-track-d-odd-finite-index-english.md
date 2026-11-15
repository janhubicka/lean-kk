# Track D — all selected odd cuts have a finite indexed complete-L+ structural witness

15 November 2026. English-first proof and hostile audit (BEFORE Lean).

## Source dependencies and status
This PR is stacked on draft [Track D #239](https://github.com/janhubicka/lean-kk/pull/239),
which proves that every selected ODD numerical-H cut in a true Henson
AlgorithmRun has a genuine (I1) or (I2) structural event at the SAME
full pre-cut closure `Z_c=closure(Run.I(c+1),X)`. That is still
under exact-head CI and must not be treated as a verified upstream
dependency until the gate passes.

Already verified and merged into `lean-kk`:
- `finiteNumericH_actualRun_uniform_exhaustive_source_index`,
  in `Kk/NumericHExhaustiveRunIndex.lean`, constructs ONE finite
  `params : Finset (AdmissibleKptNode family)` enumerating the
  entire FINAL full closure `closure(Run.I 0,X)`, with a Boolean
  `presentAt c i` mask for actual stage closure at every cut c.
  This is an actual Kpt-node enumeration, not a noncanonical
  seed/meet recipe or selected-active-branch approximation.
- `finiteNumericH_run_structural_I1I2_iff_active_node_or_fork`,
  in `Kk/NumericHStructuralCutClassifier.lean`, identifies
  the TRUE full source structural (I1) or (I2) event at a cut with
  precisely the following finite indexed alternative:
   A. One active Kpt node has level c.
   B. Two active Kpt nodes strictly cross c, have IDENTICAL complete
      old dependent-L+ raw records, and DISTINCT complete next-cut
      dependent-L+ raw records (including all auxiliary E and
      negative ordinary L atoms).

The statement is for one true finite numerical-H AlgorithmRun,
not a global diary orbit theorem.

## Main theorem (conditional-on-the-finite-index structure)

Given the real K_ell-free Henson numerical-H model with a true
AlgorithmRun and actual top seed, any ODD selected physical cut
`c=2a+1<top,N`, and ANY finite actual node enumeration `params`
with the exact final-closure membership predicate and EVERY
per-cut real membership mask `presentAt` satisfying their
two displayed coverage conditions, the above A-or-B finite
indexed certificate HOLDS.

No no-(I1), no-(I2), no-(B3), or selected-profile hypothesis
is inserted. (I1) or (I2) is a *conclusion* of the stacked
odd-structural theorem. The finite-index classifier then
translates it EXACTLY into one or two live finite indices.

## Stronger constructed-index theorem

The same conclusion holds with NO externally postulated
`params` or `presentAt`: the verified
`finiteNumericH_actualRun_uniform_exhaustive_source_index`
first supplies their finite existence and exact membership
across all stage cuts. Thus every selected odd cut has a
strictly finite, physically indexed structural witness.

The finite index is globally uniform for all cuts of ONE run,
not just a different arbitrary index at each cut. This is
essential for a future check that every allowed odd I1/I2
event falls in the retained `I` set of the direct
small-independent upper proof.

## Proof

1. Apply the stacked true Henson odd-selected structural theorem
   to the exact real run and obtain
   `KptI1AtCut family Z_c c / KptI2MeetAtCut family Z_c c`.
2. Apply the already merged
   `finiteNumericH_run_structural_I1I2_iff_active_node_or_fork`
   on exactly the same `Z_c`, `params`, `presentAt`.
   The LHS is the structural disjunction just obtained;
   the RHS is the desired one-index endpoint or two-index
   complete old-equal/upper-different fork.
3. For the constructed version, invoke the verified uniform
   exhaustive index theorem on the actual run and original
   seed pool (coerce `U : Finset (Fin N)` to
   `U : Set (Fin N)`). Obtain `params,presentAt`,
   exact final-closure membership, and exact stage presence
   at all cuts. Discard the extra injectivity/exhaustiveness
   components only AFTER obtaining the exact equalities.
   Apply (1)--(2) to the constructed index.

## Hostile checks

1. Distinguish `R.I(c+1)` used for pre-cut stage closure from
   `R.I 0` used for FINAL node index. This subtlety has
   caused previous actual-vs-final source errors.
2. The index enumerates ACTUAL Kpt nodes, including generated
   E parameters and meets, not selected graph originals.
3. The two-index condition includes BOTH crossing inequalities
   `c<level(z_i)` and `c<level(z_j)`.
4. The compared records are complete `RawPartialTypeNode`
   values and include auxiliary E and negative L data; no
   projection to ordinary positive neighbour masks.
5. Under a genuine I1 node, the literal `KptI2MeetAtCut`
   may be true by a trivial self-meet, but there need not be
   any two-strictly-crossing fork. The exact classification
   keeps the disjunction (I1 node) OR (full fork).
6. Do NOT say `I2 iff fork` without assuming no I1.
7. The common original base E is assumed symmetric,
   irreflexive and K_ell-free, as required by the stacked
   #239 numerical-H theorem.
8. The cut coordinate c is PHYSICALLY odd and below the
   run top and finite carrier. This is not arbitrary
   reindexed parity.
9. A real top Kpt seed is explicitly required for the true
   selected-level I3/structural dichotomy.
10. The uniform index theorem assumes genuine seed
    representation `X ⊆ ambientPrefixPool(...,U)`;
    do not replace with all prefixes as initial SEEDS:
    that forces all levels I1 and destroys boundedness.
11. Finite existence of an index is *not* a computable formula
    for the specific retained macrodiary; it must be
    instantiated/compared across the intended recursion.
12. Equality of active index old records does not imply
    equality of corresponding next records; this difference
    is precisely the finite I2 certificate.
13. A selected odd physical cut need not be skippable!
    Its structural witness can justify retaining its
    parameter free level even though ordinary L(c,-)=false.
14. Odd corrected B3 itself is independently checked in
    target PR #223; this proof instead leverages the true
    actual-run odd structural implication, not the mere
    statement "odd no L edges => boring".
15. Neither theorem gives the labelled inverse-source
    orbit, relative graph-age loss, or the final BRD
    characterization; those remain separate pending claims.
16. The supplied source names require exact qualified
    strict axiom registration, and the stacked #239
    dependency must first pass its own hosted Lean gate.

## Lean implementation

New `Kk/ActualRunOddFiniteIndex.lean`, importing
`Kk/ActualRunOddStructural.lean`,
`Kk/NumericHStructuralCutClassifier.lean`,
`Kk/NumericHExhaustiveRunIndex.lean`.

Define `KptFiniteStructuralCutCertificate` as the precise RHS
of the checked structural index theorem. State/prove:

1. `henson_actualRun_odd_selected_has_indexed_I1_or_I2`
   with explicit params and presentAt representation.
2. `henson_actualRun_odd_selected_has_constructed_indexed_I1_or_I2`
   using the checked uniform exhaustive node index and
   the first theorem.

A dedicated exact-head strict transitive-axiom gate should
compile the new module and print both theorem names,
with only standard axioms. Keep the PR stacked/draft
until predecessor and current gates are green.
