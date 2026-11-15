# Track G — actual bare-root old-range *off-plan* finite source certificate

**15 November 2026. English-first mathematical proof and adversarial review, prior to the Lean module.**

This develops the open **physical finite-index application** (item 15 of `docs/track_e_allowed_extra_cut_mask_english_audit.md`). It reuses, rather than reproves, the exact genuine-run and cross-height arguments of Tracks C/E. All definitions below are in the **same normalized Kpt tree** and compare **source-coordinate cuts**, never mere graph-age-shadow positions.

## G1. Precise finite criterion

Let `X ⊆ Y` be *literal* sets of admissible Kpt nodes, with AlgorithmRuns `R_X` and `R_Y` and actual scan tops `t ≤ t'`. Assume **a real seed at level t lies in X**. For each cut `c<t`, let

- `Z_X(c) = closure_(R_X.I(c+1))(X)`;
- `Z_Y(c) = closure_(R_Y.I(c+1))(Y)`.

Suppose two independent exact finite indices `(node_X,live_X)`, `(node_Y,live_Y)` enumerate *all* nodes of `Z_X(c)` and `Z_Y(c)` respectively, at each old cut. The index types `Fin P`, `Fin Q` may have different sizes. Fix an explicit set `Allowed` of permitted extra cut coordinates; it must include every physical auxiliary microevent **intended** in the refined diary. The finite off-plan certificate is:

For every `c<t` such that `c∉R_X.I c` and `c∉Allowed`:

1. For each live new index `j` with `lev(node_Y(j))=c`, there is **some** live old index `i` with `lev(node_X(i))=c`.
2. For each live new index `j` having both the actual raw full old type `T` at `c` and actual full upper type `U` at `c+1`, there is **one and the same** live old index `i` witnessing both `T` and `U`. The records contain all dependent binary/unary/diagonal atoms, auxiliary `E`, negative bits and all I2 fork choices.

The finite-index predicate *only* requires these checks at old-boring **and** disallowed cuts; prior all-cut certificates were unnecessarily strong for a resolved diary that intentionally introduces microevents.

## G2. Abstract two-index theorem (full proof)

Assume the hypotheses above, including the two actual exact-index equalities. At any off-plan old-boring cut `c`, show `NewRootNoNoveltyAtCut family Z_X(c) Z_Y(c) c`:

- If `Z_Y(c)` contains a terminal at `c`, use the new exact live index to find `j`, then the terminal part of the finite certificate to find old live `i`, then old exactness to obtain an old terminal at `c`. This is precisely the `KptI1AtCut Z_Y → KptI1AtCut Z_X` conjunct. **No node identity** is needed.
- If `(T,U)` is in the full physical new crossing relation, exact new indexing gives one live `j` realizing **both** types. Invoke the finite pair certificate to find one old live `i` realizing both; exact old indexing puts that node in `Z_X(c)`. Thus the entire new crossing *relation* is contained in the old relation. **Do not** reason separately from marginal old/upper type sets.

Apply `crossheight_old_range_sandwich_of_offplan_no_novelty`, whose proof was checked independently by Track E, to obtain for all `i≤t`:

`R_X.I i ⊆ R_Y.I i`, and

`{q∈R_Y.I i : q≤t} ⊆ R_X.I i ∪ {q : q∈Allowed ∧ i≤q}`.

This is an **inclusion**, not equality at allowed cuts and not preservation of labelled inverse fibres. No events above `t` are constrained.

## G3. Physical numerical-H+ application (full proof)

Assume two concrete numerical models `K,L`, old/new finite heights `N≤M`, old-prefix block-position alignment, `k>0,j>0`, real new top `hPosition(k,j,k)<M`, the correct bounded cutoff `N≤hPosition(k,j-1,k)+1`, exact equality of all old binary/unary/diagonal atoms, both actual forbidden-family avoidance certificates, and `X⊆ambientPrefixPool` for the actual old model. Assume `HasPhysicalExhaustiveKptRun family X oldTop`.

1. Unpack this last witness to obtain `R_X`, a **real old-top seed**, a finite old source index and exact old pre-cut live masks.
2. By `finiteNumericH_bareTopRoot_has_physical_exhaustive_run`, construct the new **bare** seed `Y=X∪{actual top original}`, an actual new AlgorithmRun `R_Y), and a separate complete finite index. Here **no preinsertion** of old parameter closure occurs.
3. The checked `finiteNumericH_old_physical_top_le_new_chronological_top` derives `oldTop ≤ newTop` from the real old-top seed and the physical cutoff.
4. Restrict the new exactness to `c<oldTop`, using `oldTop≤newTop`. Seed inclusion `X⊆Y` holds definitionally.
5. With those *constructed* two indices, the finite off-plan certificate from G1 is a decidable-looking **hypothesis**, not a conclusion of old-base fidelity. The abstract theorem of G2 gives the desired selected-level sandwich.

No `Fin oldParams.card ≃ Fin newParams.card` is manufactured. In particular this theorem creates genuine **physical** source-index witnesses and characterizes what still has to be checked for the chosen finite resolved diary.

## G4. Hostile audit and mathematical boundaries

1. False shortcut: full equality `R_X.I i=R_Y.I i` at different tops. Need the old-range restriction.
2. False shortcut: only ordinary L and selected-front age are compared. Need complete old+upper **dependent L+** pairs.
3. False shortcut: terminal witness must be the *same* node. Event classification only needs existence at the level.
4. False shortcut: marginal old-type and upper-type covers imply joint cover. They may be supplied by **different** nodes; require one old index witnessing both types.
5. False shortcut: collapse all I2 forks to a deterministic next-type map. The crossing is a **relation**, not a function.
6. False shortcut: require quietness at already-interesting or *permitted* cuts. That needlessly prohibits legitimate auxiliary microevents such as K4 cuts 10 and 22 (with selected x=38 in the regression).
7. False shortcut: the source coordinates of independent numerical-H models are aligned merely because the physical original graph ages agree. Our common Kpt-tree and exact old-atom assumptions are explicit; global cross-occurrence normalization remains open.
8. False shortcut: a finite index with arbitrary cardinal bound gives a fixed universal finite **orbit carrier**. Its size depends on the physical run and does not provide monoid transport.
9. False shortcut: all-source pair covers follow from preserved raw support age or chosen clique-block stage. The proof retains them as additional hypotheses.
10. False shortcut: this theorem validates the global upper or lower BRD. It does not prove infinite coherent scheduling, correct full-(B3)-relative-continuation loss, labelled source orbits or unavoidability.
11. Boundary case `Allowed=∅`: off-plan quietness need be checked **only at old-boring cuts**; old-range equality follows as a separate corollary if desired.
12. Boundary `oldTop=0`: no old cuts are tested; the only old-level result is the real top inherited by the new run. This is consistent.
13. Do not add a GREEN mark to the proposed resolved-copy theorem or any of the 12 global PENDING claims.

### Two further adversarial stress tests

**Coordinate projections are insufficient.** For an abstract old crossing
relation `{(0,0),(1,1)}` and a new crossing pair `(0,1)`, both
marginal coordinates of the new pair occur among old pairs, yet
the *joint* pair is not present in the old crossing relation. In the
actual Kpt theorem this is prevented exactly by requiring one live
old index to witness the complete old *and* upper dependent L+
type together, rather than two unrelated index witnesses.

**Vacuous Allowed set.** Taking `Allowed = Set.univ` makes the
off-plan finite tests vacuous. To extract a uniform finite envelope
or Ramsey bound from the sandwich, one must separately construct
an **occurrence-independent bounded finite event template** from
the *fully refined* diary, including genuine auxiliary q2 cuts,
and prove coherent transport of its source coordinates between
occurrences. The conditional finite theorem does not establish
that finite-template property; its input `Allowed` is arbitrary.
Even `Allowed.Finite` for each one finite occurrence is insufficient
for a bound uniform across all occurrences of a fixed diary.

**Terminal simplification to explore (not a source theorem here):**
an old-boring cut cannot carry an old terminal source (since that
would force old I1 interestingness). Thus the off-plan old-terminal
witness condition may be replaced by *absence of any new terminal*
there, once exactness of the old AlgorithmRun is available.
This is a possible next simplification for verifying the physical
certificate, not a claim that the bare-root construction already
ensures the absence of all dependent terminal nodes.

## G5. Proof-check acceptance

The new module should be compiled on an *exact head* and its two named theorems checked by `#print axioms`, requiring only `propext`, `Classical.choice`, `Quot.sound`. Until the CI passes, no manuscript source pin or marker status changes. If it passes, cite both the abstract off-plan finite-index certificate and its genuine bare numerical-H+ application as **BLUE** interfaces in olive text, and leave the global PENDING marks untouched.
