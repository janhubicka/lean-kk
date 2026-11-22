# Track A/G — indexed structural budget for genuinely bad odd Kpt cuts

22 November 2026. English-first proof and adversarial audit BEFORE Lean.

## Aim and verified inputs

The independently Lean-verified and merged theorem
`finiteNumericH_odd_exact_bad_has_three_physical_witnesses`
(Track A/G PR #481) describes a genuinely bad odd numerical-H
cut of an old-factor comparison. For the TRUE candidate pre-cut
parameter closure, any exact Bad event has:
1. a genuine terminal I1 node of level c;
2. two genuine live nodes in one component meeting at level c;
3. a crossing new node with no OLD live source having its
   exact COMPLETE old dependent Kpt ancestor at c.

The theorem is relative to one actual old AlgorithmRun on seed
X, a potentially larger source Y, and a *finite exact candidate
Kpt index*. It is not a two-run profile-equality theorem and it
does not assert the third obstruction disappears.

## Finite structural-level envelope

Fix a finite index
  node : Fin Q -> AdmissibleKptNode family.

Define the finite set of *possible structural cut levels*:

  S(node) =
    { lev(node i) : i in Fin Q } UNION
    { lev(meet(node i,node j)) : i,j in Fin Q }.

The second image may contain arbitrary ordered pairs; those with
nodes in different components or inactive at a particular cut are
deliberate over-approximations. These inclusions are safe because
the trichotomy's I2 witnesses always belong to the same component.

**Theorem 1.**  |S(node)| <= Q+Q^2.

**Proof.** The first image has at most Q members. The image from
Fin Q × Fin Q has at most Q² members. The cardinality of a finite
union does not exceed the sum of the cardinalities. No injectivity
of the source index is needed. This is a purely finite combinatorial
fact; it does NOT prove Q is diary-uniform.

## The residual missing-old-socle set

For the same actual old run R on X and candidate seed Y, at each
cut c<top define Missing(c) if a live candidate indexed node
z=node i crosses c but has NO actual old-live source node w in

  closure(R.I(c+1), X)

with cut<lev(w) and COMPLETE equality of old ancestor nodes

  ancestor_c(z) = ancestor_c(w).

Define M_odd as the finite set of ODD cut numbers c<top for
which Missing(c) holds, *irrespective of whether c is Bad*.
This is deliberately a conservative over-approximation and uses
the true old closure, not just the original graph reduct.

The exact odd Bad set B_odd consists of all numbered odd
cuts c=2a+1 that belong to the actual old-factor Bad cut set.
All such c automatically satisfy c<top by the verified Bad cut
membership lemma.

**Theorem 2.** For an exhaustive candidate index at EVERY
actual odd Bad cut,

  B_odd subset S(node) union M_odd,

and hence

  |B_odd| <= Q + Q² + |M_odd|.

**Proof.** Take c in B_odd, so c=2a+1 and the actual Bad
predicate holds. Apply the verified odd-cut trichotomy.

- If a terminal z exists, exact candidate index coverage gives
  some i with node i=z, hence c=lev(node i) belongs to S.
- If a same-component meet of z,w exists, exact coverage gives
  i,j with node i=z,node j=w; then
  c=lev(meet(node i,node j)) belongs to S.
- Otherwise a crossing z lacks an old complete cut ancestor.
  Exact coverage gives an active i naming z. Therefore c
  belongs to M_odd by definition.

This proves the finite-set inclusion. The cardinality bound
follows from Theorem 1 and the ordinary union inequality.

**Strong zero-missing corollary.** If every indexed live
candidate crossing at every odd c<top has some old
complete lower-ancestor socle witness, then M_odd=empty,
and |B_odd|<=Q+Q². Bad odd cuts outside S(node) are
impossible. This does not eliminate terminal or meet cuts.

## Adversarial controls

1. The cut c is an actual NUMERICAL-H level, not the original
   generation index g. No `hPosition` identification is needed
   for the odd-cut theorem.
2. The actual exact Bad set is relative to an OLD
   AlgorithmRun and its old factor F. The theorem does not
   hypothesize a separate Y AlgorithmRun.
3. The candidate finite index must cover the COMPLETE actual
   candidate parameter closure at EVERY cut used in the
   bound. One source list on initial seeds alone is not enough.
4. The index may be noninjective or contain nodes inactive at
   certain cuts; overcounting is harmless.
5. The terminal set includes the genuine Kpt level of each
   candidate indexed node, not an original vertex's
   generation or ordinary-L type height.
6. Meet levels of all ordered node pairs overcount genuine I2,
   but every actual I2 witness is included. No false equivalence
   between equality of old prefix and same-component meet is used.
7. The missing-old-socle set includes some cuts not Bad. Thus
   only an UPPER bound is claimed, not exact classification of
   all Bad cuts by the three finite lists.
8. The old witness w must lie in the actual old
   `closure(R.I(c+1), X)`, not in candidate Y or a selected
   ordinary-L shadow.
9. The old ancestor equality is equality of actual Kpt nodes,
   including dependent auxiliary E and negative L; an L-only
   common-neighbour test would be insufficient.
10. The full true stage-original zero L condition needed by the
    general theorem holds automatically for odd cuts by
    `hNumericBinary_odd_left_false`, even if auxiliary E is
    nonzero there.
11. The finite index Q can depend on the numeric carrier and
    resolved source; no uniform bound on Q is derived.
12. `M_odd` is finite because only c<top are included, but its
    cardinality need not be bounded by a diary invariant.
13. The result does not compare arbitrary different scan tops
    or establish a common labelled inverse-source orbit.
14. For Q=0 the structural set is empty; if any Bad odd cut
    existed the exact-source trichotomy would force a live
    candidate source and contradict exhaustiveness. The
    theorem therefore handles the empty index without
    manufacturing a node.
15. Replacing the candidates' full old/upper crossing relation
    by a FUNCTION would wrongly discard possible I2 forks.
    The trichotomy/ledger keeps the entire genuine source.
16. The resulting count is not the number of ALL interesting
    Kpt cuts. It is a quantitative bound on exact old-factor
    Bad odd cuts for one specified old run and candidate index.
17. Neither a diary-uniform finite Ramsey upper bound nor
    the exact BRD formula follows until Q and M_odd are
    controlled from the resolved diary.
18. No frozen black manuscript text or validation marks are
    modified until the new Lean source passes exact-head
    direct/full build and standard-only named axiom inspection.

## Lean implementation

Create `Kk/TrackAOddIndexedStructuralBudget.lean` importing
`Kk.TrackAOddBadSocleTrichotomy` and `Mathlib.Tactic`.
Name the finite structural envelope, the odd missing-socle
cut set, and the odd exact-Bad cut set.

Kernel-check:
- `kpt_indexed_structural_levels_card_le`
- `finiteNumericH_odd_bad_off_indexed_structural_has_missing_socle`
- `finiteNumericH_odd_bad_subset_structural_union_missing`
- `finiteNumericH_odd_bad_card_le_structural_plus_missing`

If a genuinely strong `M_odd=empty` special case is cheap,
add it after the general theorem. Exact-head GitHub CI must
run direct module build, full `lake build`, strict qualified
axiom reports. Until then all submitted source remains unverified.
