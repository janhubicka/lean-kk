# Track A/C/G — automatic candidate index and ONE complete RAW old-seed match per candidate odd frontier

22 November 2026. English proof FIRST. This note is deliberately
a *composition* of three independent source results:

1. Already merged Track E E70
   `finiteNumericH_oldRun_candidate_uniform_exhaustive_source_index`
   constructs one exhaustive candidate index on the TRUE OLD
   AlgorithmRun's pre-cut closure tails, with NO candidate Y-run.
2. Already merged Track A/G PR #503
   `finiteNumericH_odd_bad_card_le_of_max_lower_socles`
   bounds true old-factor Bad odd cuts by Q+Q² if each candidate
   name has a complete OLD lower-socle witness at its MAXIMAL
   odd old-boring live crossing.
3. Exact-head checked Track A/C PR #509 (clean-source successor of original PR #507)
   `finiteNumericH_candidate_below_original_old_socle_of_raw_seed_match`
   turns one complete old RAW numerical-H type equality with
   an actual old seed into a lower Kpt-ancestor witness for
   an arbitrary candidate node BELOW the target physical original.

## New application-facing statement

Take an actual finite numerical-H+ graph-signature model
`A=finiteNumericH K k N` with genuine family avoidance and
literal ordinary-L symmetry, a source original pool U⊆Fin N,
old seed X and candidate seed Y with X⊆Y and candidate Y
contained in the actual represented ambient prefix pool.
Let R be a genuine old AlgorithmRun on X at scan top.

Then there exists a finite set `params` of genuine dependent
candidate Kpt nodes and an exact live mask
`live : Nat -> Fin params.card -> Bool`
enumerating the TRUE closures `closure(R.I(c+1),Y)`
at every actual source cut c<top.

Let z_j denote the j-th actual candidate node and define C_j
to be precisely its genuine ODD, OLD-BORING, LIVE CROSSING cuts.
For every j where C_j is nonempty, put m_j=max(C_j).

Assume the concrete finite RAW witness condition:

  for every such j, there exists a genuine physical original
  v_j in Fin N such that

    z_j <= A.kptOriginal(v_j)

  and a true old-seed RAW prefix match

    KptRawOldSeedMatchAt family K k N hAvoid X v_j m_j.

Then the true old-factor Bad ODD cut set of that SAME old
AlgorithmRun with the CONSTRUCTED candidate index satisfies

    |BadOdd| <= Q + Q², where Q=params.card.

This statement does NOT assume a target AlgorithmRun on Y,
a candidate source-index existence premise, or full upper
Kpt crossing equality.

### English proof

By E70 obtain params, live and exact candidate pre-cut
coverage. For each name j with C_j nonempty, m_j∈C_j
and hence m_j < lev(z_j).
The stated physical raw witness provides v_j and the
old-seed match at m_j. Apply the descendant raw-seed
theorem #507 to obtain
  KptActualOldSocleCoveredAt family X top R z_j m_j.
These are exactly the per-candidate maximal lower
socle hypotheses of verified #503. Using the same
params, live, hAvoid, symmetry and exact closure
coverage, its cardinality conclusion follows.

The theorem uses only one full dependent RAW prefix equality
per relevant candidate name. That is a concrete finite
condition for a resolved diary construction to target,
though its truth from diary axioms is NOT established.

## Hostile audit

1. The witnessed z_j need not be a physical original;
   z_j<=O_v is explicit, not inferred from type equality.
2. The raw seed match uses a TRUE old seed x∈X below some
   actual old original O_u. A matching candidate seed in Y
   is not enough.
3. Physical raw type equality is COMPLETE old Kpt
   `partialTypeAt`, including E directions, negative L
   atoms and type-vertex data, not ordinary graph adjacency.
4. The certificate is taken at m_j, the maximum of the
   candidate's TRUE OLD-BORING ODD LIVE crossing set,
   not at max possible cut, max graph age or max original index.
5. C_j may be disconnected. Verified E79 downward old
   socle closure monotonicity supplies all lower eligible
   cuts from the one maximal witness.
6. The candidate index is constructed on OLD R.I(c+1)
   tails; no target Y AlgorithmRun is assumed, avoiding
   circularity in source matching.
7. No source-index bijection with original graph vertices
   is required; the existential v_j may differ among
   names and may be nonunique.
8. Every indexed candidate is a genuine admissible Kpt
   node; meet and parameter-generated auxiliary E nodes
   are not silently discarded.
9. At a cut with terminal z_j (lev(z_j)=cut), the
   crossing condition excludes it from C_j. Those
   terminal levels remain in the Q+Q² structural set.
10. The I2 meet alternatives also remain; no no-I2
    assumption or crossing-relation functionalization.
11. Q depends on finite numerical carrier N and Kpt
    closure; it is NOT bounded uniformly by this theorem.
12. The existence of an old raw seed-type match for each
    maximal j is a genuine remaining hypothesis. It may
    fail for K4 auxiliary q2/E exceptions; no automatic
    success is asserted.
13. The resulting bound counts old-factor Bad ODD cuts,
    not all selected levels in a newly constructed run.
14. The existing Track E E70 and PRs #503/#507 are
    verified separately, but the combined Lean result
    needs an exact-head build of its OWN.
15. The statement does not establish cross-diary common
    labelled source or exact BRDs. Frozen black TeX and
    validation marks remain unchanged.

## Lean acceptance

Create `Kk/TrackARawMaxOddBudget.lean` importing
`Kk.TrackAOddOldSocleFrontier`,
`Kk.TrackACandidateDescendantRawSocle`, and
`Kk.TrackECandidateSourceFiniteIndex`.

Main endpoint:
`finiteNumericH_odd_bad_budget_exists_of_raw_max_candidate_seed_matches`.

The output should EXISTENTIALLY return params, live, exact
source closure indexing, and implication from the one-RAW-match
per candidate maximal cut to `BadOdd.card <= Q+Q²`.

No global BRD theorem, no artificial `sorry`, no source
index size claim. Run dedicated direct module/full Lake and
strict qualified standard-only axiom gate. The source is STACKED against PR #509 and must be rebased
against main after that PR merges;
do not silently duplicate its theorem.
