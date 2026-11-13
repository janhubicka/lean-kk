# Track A — exact reference integer age from common old-neighbour clique capacities

**13 November 2026. English proof and hostile audit BEFORE formalizing.**
This is an independent continuation on integrated main; it is not a claim
that Track B has generated an unbounded compatible resolved-copy schedule.
No protected manuscript or centralized validation marker is changed.

## The finite reference graph and its labelled old columns

Fix an integer `ell>=1`, a number of future sorts `d`, an ordinary
Boolean directed adjacency table `E:Nat→Nat→Bool`, finite *disjoint*
pools P (old vertices) and W (future vertices), a total sort map
`tau:Nat→Fin d` on W, and a complete old-column function
`c:Nat→Fin d→Bool`. Require for EVERY p∈P and w∈W, in BOTH
orientations,

```text
E(p,w) = c(p,tau(w)) = E(w,p).
```

No assumption that different future vertices have distinct labels.
The induced old graph on P must be K_ell-free. The induced graph W
may have arbitrary internal edges; its K_ell-freeness is tested
separately. No claim that E is globally symmetric is needed beyond
these two explicitly matching crossing directions, because the
finite directed-clique predicate tests each orientation.

For any nonempty support T⊆Fin d, |T|≤ell−1, define its **common old
neighbourhood**

```text
R(T) = {p∈P : for all t∈T, c(p,t)=true}
rho(T) = maximum cardinality of a directed E-clique in R(T)
B(T) = ell−1−rho(T).
```

The maximum is the *actual* clique capacity of the common
neighbourhood, NOT the cardinality of R(T). This definition is
meaningful for ell=1 as well (there are no nonempty allowed supports).
If some B(T)=0, the future sort configuration is not an admissible
graph-age function in the manuscript's normalized >=1 sense;
this is a legitimate empty-extension phenomenon, not a reason
to assume positivity.

## The exact per-pattern theorem

Provided P is K_ell-free and P∩W=∅,

```text
K_ell-free_E(P∪W)
iff
K_ell-free_E(W) and
  for every directed clique s⊆W and every admissible nonempty T:
     |{w∈s : tau(w)∈T}| ≤ B(T).
```

This is an iff for **every finite W and every internal W edge pattern**
with the fixed complete old-column data c. Neither the existence of
a physical simultaneous front nor its auxiliary E records is inferred.

### Forward proof

Assume P∪W has no forbidden clique. Fix an E-clique s⊆W and
an allowed T. Let s_T be its T-labelled subclique. The exact finite
capacity is achieved by a clique r⊆R(T) with |r|=rho(T). For each
p∈r and w∈s_T, the complete old-column hypothesis gives both
E(p,w)=E(w,p)=1, since tau(w)∈T and p∈R(T).
Because P and W are disjoint, r∪s_T is an E-clique contained
in P∪W, hence has cardinality strictly below ell.
Thus rho(T)+|s_T|<ell, giving |s_T|≤ell−1−rho(T).

### Converse proof

Assume W is K_ell-free and all support inequalities hold.
Suppose an E-clique H⊆P∪W of cardinality ell exists. Decompose
H=H_P∪H_W with H_P=H∩P and H_W=H∩W; the two parts are disjoint.
P and W being K_ell-free force H_P and H_W to have cardinality
strictly below ell and in particular H_W is nonempty (otherwise
H⊆P would be forbidden).

Take the **actual set of labels occurring** in H_W,

```text
T = {tau(w):w∈H_W}.
```

This support is nonempty and has size at most |H_W|≤ell−1,
so it is an allowed nonempty support in `IntegerGraphSupport`.
Every p∈H_P is adjacent to every w∈H_W; the full typed-column
hypothesis therefore puts p in R(T). It follows that
|H_P|≤rho(T). Every vertex of H_W lies in T, so the support
inequality gives |H_W|≤ell−1−rho(T). Summing yields
ell=|H_P|+|H_W|≤ell−1, contradiction.

**Truncated-subtraction guard (essential).** As R(T)⊆P and P is
K_ell-free, rho(T)≤cap(P)<ell. Thus rho(T)≤ell−1 and the
natural-number difference ell−1−rho(T) has its intended arithmetic
meaning. The converse proof MUST explicitly derive rho(T)<ell
before deriving the contradiction from the truncated bound; without
this, the last omega step has a legitimate countermodel with
rho(T)≥ell and bound 0. This was caught by the first Lean compile.

This proof also works if H_P is empty: then H⊆W already
contradicts the assumed K_ell-freeness of W.

## Joint canonicalization and integer graph-age effect

Let `G_B=integerGraphAgeCanonical d ell B`, using the existing
verified finite integer-witness canonicalizer. For each K_ell-free W,
the previously verified
`finiteClique_all_constraints_integerCanonical_iff` establishes
that the **whole system of all-support inequalities** for its cliques
is unchanged when B is replaced by G_B.
Therefore the exact physical reference test also has the iff

```text
K_ell-free_E(P∪W)
iff
K_ell-free_E(W) and
  for every clique s⊆W and every admissible T:
     |s_T| ≤ G_B(T).
```

This does not assert B=G_B pointwise. It also does not assert G_B
is a *genuine positive graph age* unless there is an independently
verified admissible age below B. Positivity/singleton feasibility
must not be fabricated.

This provides the **missing finite reference-table age adapter** for
Track A at the level of arbitrary finite W: it uses capacities
computed from the **actual old past** and the **complete old labelled
columns**, rather than presupposing a graph-age F matching a
fixed finite occurrence. Instantiating it on the real numeric old
prefix still needs Track B's concrete compatible columns and,
to identify a *chosen target cover*, an equality of the computed
canonical G_B with the manuscript's intended F at every support.

## Hostile adversarial tests

1. **Old cardinality is not capacity.** If R(T) contains many
   pairwise nonadjacent old vertices, rho(T)=1 rather than |R(T)|.
   Replacing rho by cardinality rejects valid K_ell-free
   continuations.
2. **Mixed support is essential.** For ell=3, P={p} and sorts x,y,
   c(p,x)=0, c(p,y)=1, the bounds are
   B({x})=2, B({y})=1, B({x,y})=2.
   An x-y edge is allowed. Adding a reserved q with q-x=1 and
   q-y=0 preserves the mixed upper bound; incorrectly q-y=1
   lowers B({x,y}) to 1, exactly the P4 whole-front obstruction.
3. **Crossing BOTH directions:** even if E(p,w)=1, a missing
   reverse arc invalidates the directed clique-combination
   argument. The two equalities are explicit.
4. **Disjoint P/W:** without disjointness the cardinal additivity
   |r∪s_T|=|r|+|s_T| fails, so the raw bound formula can be wrong.
5. **Every T, not just support of one selected sort:** the
   inequalities must hold jointly over all nonempty supports.
   The older graph can realize different rho(T) values on
   singleton and mixed supports.
6. **Sort multiplicity:** T is a set of labels but s may contain
   several vertices of each sort; the inequality counts all
   such vertices. Injectivity of tau is neither assumed nor needed.
7. **Empty support:** empty future clique is handled by P's
   K_ell-freeness; T ranges over NONempty allowed supports only.
8. **Zero bound possible:** if P contains a clique of size
   ell−1 adjacent to a future sort, B({x})=0. A normalized
   positive age needs extra eligibility; the generic bound
   still correctly forbids inserting any x vertex.
9. **W K-free independently:** constraints for support T alone
   do not exclude a forbidden K_ell already inside W when
   support count normalization only ranges up to ell−1.
10. **No automatic physical occurrence:** the theorem holds for
    every finite labelled W as a *glued abstract graph*, but a
    single fixed set of actual top originals cannot be treated as
    containing every such W pattern. Use the separately verified
    pinned-prefix realization theorem for individually compatible
    patterns; the unbounded canonical resolved schedule still
    belongs to Track B.
11. **Not H+ B3:** no auxiliary E incidence, full dependent
    source assignment or common labelled orbit follows.
12. **No unstated global symmetry:** only full crossing-column
    equality is needed for the directed argument, and no
    loopy/antisymmetric claims are added to the old/future tables.

## Lean endpoints and gating

New module `Kk/FiniteOldColumnAge.lean` will supply
`oldSupportCommonNeighbourPool`,
`finiteOldColumnRawBound`,
`finiteOldFuture_free_implies_raw_support`,
`finiteOldFuture_free_of_all_raw_support`,
`finiteOldFuture_free_iff_raw_support`, and
`finiteOldFuture_free_iff_canonical_support`.

Lean proof reuses
`finiteDirectedCliqueCapacity_attained`,
`finitePoolCliqueCheck_false_iff_capacity_lt`,
`finiteClique_card_lt_of_pool_cliqueFree`, and
`finiteClique_all_constraints_integerCanonical_iff`.
Run explicit module build, strict *fully qualified* transitive-axiom
audit, and full `lake build` on exact PR head. No global manuscript
validation mark without a checked physical instantiation.
