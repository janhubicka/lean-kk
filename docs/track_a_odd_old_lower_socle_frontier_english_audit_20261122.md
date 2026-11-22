# Track A/G: one MAXIMAL old Kpt socle witness per candidate for ALL odd old-boring cuts

22 November 2026 — **English proof first**, then Lean, with hostile audit.
This is a specific improvement of the merged odd Bad-cut bound in
`Kk.TrackAOddIndexedStructuralBudget` and automatic indexing in
`Kk.TrackAOddAutomaticIndexBudget`.

## The actual source problem

Fix an ACTUAL old AlgorithmRun R on seed X at one scan top N,
and a finite exact candidate index
  node : Fin Q -> AdmissibleKptNode family,
  live : Nat -> Fin Q -> Bool,
which names the actual full candidate pre-cut closure on Y along
the OLD selected-level sets R.I(c+1). No Y-run is postulated.

For a candidate node z and an actual cut c, say **old-lower-covered(z,c)**
if z crosses c and SOME OLD-LIVE source node w crosses c, belongs to
  closure(R.I(c+1), X),
and satisfies the equality of COMPLETE dependent lower Kpt ancestors
  ancestor_c(z)=ancestor_c(w).
This retains auxiliary E and all negative graph atoms, not just
ordinary clique capacities. It is strictly weaker than old-UPPER
ancestor coverage used in Track E's maximal frontier theorem.

For each name j in Fin Q, let C_j be the finite set of odd c<N with
  * the OLD run genuinely boring at c, i.e. IsInterestingAt on its
    actual pre-cut closure is false;
  * live(c,j)=true in the candidate closure;
  * c<lev(node(j)), so the candidate really crosses.

C_j is finite and may be disconnected by selected or non-boring
levels; no interval assumption is made. If nonempty, let m_j=max C_j.

## Lemma 1: complete OLD lower socle coverage is downward-monotone

If 0<=low<=high<N and old-lower-covered(z,high), then
old-lower-covered(z,low).

**Proof:** Let w be the actual matching old node at high.
The old AlgorithmRun's final-tail identity gives
  R.I(high+1) subset R.I(low+1).
The verified `kpt_actual_run_preCut_source_mono_down` transports
w from the higher actual old pre-cut closure into the lower one.
The genuine complete ancestor identity at high restricts to
the lower level using
`kpt_LevelTree_lower_ancestors_eq_of_higher_eq`.
Both crossing inequalities at low hold by low<=high. Thus the
*same* old source w witnesses coverage at low. No new Y-run,
source bijection, or L-only projection is used.

## Lemma 2: a SINGLE maximal odd source check per named candidate

For every nonempty C_j,
  [ old-lower-covered(node(j),m_j) ]
iff
  [ old-lower-covered(node(j),c) for EVERY c in C_j ].

**Proof:** The forward implication uses Lemma 1 and
c<=m_j, with m_j<N because m_j belongs to C_j.
The reverse implication simply instantiates c=m_j.
Old boringness need not hold at intermediate levels.

## Theorem 3: all OLD-BORING odd missing-socle cuts vanish

Assume for every j with C_j nonempty there is a complete old
lower-ancestor witness at m_j. Then for any c<N such that c is ODD
and the old run is genuinely BORING at c,
`kptMissingOldSocleAt family X N R node live c` is FALSE.

**Proof:** If a live candidate node(j) crosses c and lacks an
old ancestor witness, then c belongs to C_j by the displayed
hypotheses. Its C_j is nonempty. By the maximal assumption and
Lemma 2, that node is old-lower-covered at c, contradiction.
A candidate can be inactive at higher cuts; we only propagate
from the maximum of its own *actually live and old-boring* cut set.

## Theorem 4: bound genuine factor-Bad odd cuts by structural levels

With a true finite numerical-H+ graph source, family avoidance and
symmetry, X subset Y, exact candidate-source index at each
actual pre-cut closure, and the per-node maximal old-lower-coverage
hypothesis, every genuinely exact factor-Bad ODD cut lies in the
conservative finite terminal/meet source level set:
  S(node) = {lev(node(j))} union
            {lev(meet(node(i),node(j))) : i,j in Fin Q}.
The merged source theorem bounds |S|<=Q+Q², hence
  |BadOdd| <= Q + Q².

**Proof:** A true factor-Bad cut is old boring and lies below top,
by the merged exact Bad-membership characterization.
The merged odd Bad trichotomy, in its indexed covering form, says
that every Bad odd cut either lies in S(node) or admits a
missing-old-lower-socle witness. Theorem 3 excludes the latter
at all old-boring odd cuts, leaving S(node). Use finite set
monotonicity and the checked structural-level cardinal bound.

## Adversarial audit

1. The maximal cut is taken from **each fixed source name's** true
   old-boring ODD live crossing set, not from all cuts or all names.
   Taking the wrong maximum can make the claim false.
2. C_j may be disconnected and may contain cuts in unrelated
   numerical H blocks. Downward coverage transport uses the
   actual source cut order and needs no connectivity.
3. Old-lower coverage is STRICTLY weaker than E67/E69 old-UPPER
   coverage, so this is not a duplicate of the existing stronger
   source-frontier theorem. It suffices to rule out the *missing
   lower socle* branch of odd Bad cuts, but not to construct
   equal full L+/E UPPER pairs at arbitrary nonzero stages.
4. The OLD R.I(high+1) and R.I(low+1) are used. Replacing them
   with a candidate Y-run or selected ordinary L shadow is invalid.
5. Each same-old-ancestor witness is an ACTUAL Kpt node in the
   complete old parameter-closed pre-cut source. Equality includes
   all auxiliary E records, positive and negative L data.
6. Finite candidate indexes may have duplicate node names.
   Maximal tests are per INDEX and still suffice; Q counts names,
   not equivalence classes.
7. The proof needs max cut < scan top. This follows from finite
   cut membership, never from the candidate level alone.
8. A terminal node does not cross its terminal cut, so it is
   excluded from C_j. Terminal I1 cuts remain in S(node);
   they are not declared safe.
9. Same-component I2 meets remain in S(node). The result does
   not assume no-I2, nor identify pairs merely by equal ordinary
   age profiles.
10. A factor-Bad cut is automatically an OLD-BORING cut, but the
    theorem does NOT assert every old-boring cut is Bad.
11. The new theorem bounds BadOdd for one ACTUAL old run and
    one candidate closure. It does NOT imply all Kpt interesting
    levels in either run are among these cuts.
12. Q and C_j depend on the finite physical source, numerical-H
    height and candidate index; no diary-uniform Q bound is
    silently inserted.
13. The maximal old-socle certificates must still be provided by
    the resolved diary construction; their existence is not
    proved by ordinary-L zero-column neutrality.
14. Full physical upper/crossing profile equality remains separate;
    neither a common labelled inverse-source orbit nor BRD upper
    bound is claimed.
15. The theorem MUST use real exact candidate pre-cut index
    coverage when applying the odd Bad trichotomy, not just
    a finite list of chosen originals.
16. Lean proof must pass exact-head direct/full build and strict
    standard-only qualified axiom gate. English proof alone
    earns no manuscript green mark.
17. Black frozen TeX remains untouched.

## Lean implementation

`Kk/TrackAOddOldSocleFrontier.lean`:
- `kptOldLowerSocleCoveredAt`
- `kpt_old_lower_socle_covered_mono_down`
- `kptOddOldBoringCandidateCrossingCuts`
- `kpt_odd_old_boring_lower_socle_covered_all_iff_max`
- `kpt_odd_old_boring_no_missing_of_max_lower_socles`
- `finiteNumericH_odd_bad_card_le_of_max_lower_socles`

Leverage the MERGED source helpers
`kpt_actual_run_preCut_source_mono_down`,
`kpt_LevelTree_lower_ancestors_eq_of_higher_eq`,
`mem_kptExactOldFactorBadCuts`,
`finiteNumericH_odd_bad_subset_structural_union_missing` and
`kpt_indexed_structural_levels_card_le`.

Do not merge prior to a successful named axiom parser and exact-head
`lake build`. No dependence on a Y AlgorithmRun.
