# Track E — physical BARE-root source with an old-range finite stability certificate

**15 November 2026. English-first proof and hostile audit.** Stacked on the
exact-head-green bare-root PR #205 (commit `84d040db090d002a00cec57897c8d0f0d265a00c`).
Do not promote global manuscript upper-bound claims. Black TeX is frozen.

## E49. The bare-root stage is a genuine complete physical-run witness (no arbitrary I)

Fix the genuine physical numerical H+ data of Track C/E:
`A = finiteNumericH K k N`, `B = finiteNumericH L k M`, two true forbidden-family
avoidance hypotheses, all directed/unary/diagonal old-block fidelity, the old
actual original-prefix source `X`, and one actual new original
`w = hPosition k j k` of exact free top `newTop = hPosition k (j-1) k + 1`.
The corrected new initial seeds are **exactly**
`Y = X ∪ {B.kptOriginal(w)}`.

Previous PR #205 constructs the complete bounded run on Y and its finite
exhaustive Kpt index, but exposes a gratuitous parameter `I` used only
inside the *larger auxiliary covering source* `closure_I(X)∪{w}`.
For the actual bare run no such choice is necessary: instantiate the already
verified theorem with `I = ∅`. It yields

`HasPhysicalExhaustiveKptRun family Y newTop`,

including a REAL new-top seed, the genuine canonical AlgorithmRun on Y,
ONE Finset of all genuine Kpt meet/parameter nodes, injective node names,
Boolean per-cut live masks, and exact source coverage for each cut below newTop.
The conclusion is an actual physical witness, not an existential arbitrary
run with a fake top marker.

## E50. Physical old/new finite no-novelty test

Retain an old `HasPhysicalExhaustiveKptRun family X oldTop` as in PR #205.
The genuine old-top seed and old physical prefix cover prove
`oldTop ≤ N ≤ newTop`. With E49, obtain concrete actual runs R (old) and
Q (bare new), and two *independent* exact finite indices
`nodeOld : Fin P → Kpt`, `nodeNew : Fin Q → Kpt` with live masks.
No equality of P and Q is required.

For each cut c<oldTop, consider two **new-to-old coverage tests**:

1. Every *live* new index with level exactly c has a live old index of
   level c. Only existence is tested, not terminal-node identity.
2. Every *live* new index possessing the complete paired L+ records
   `(oldAt(c), upperAt(c))` has an old live index with that same FULL pair.
   Both records of each pair come from one and the same genuine Kpt node.

Use the exact two source-index coverage equivalences, old physical top
monotonicity and literal seed inclusion `X⊆Y`. The verified
`crossheight_runs_old_range_eq_of_two_finite_index_cover` gives, for
every `i≤oldTop`, the exact height-filtered equality

`R.I i = {q | q∈Q.I i ∧ q≤oldTop}`.

This is strictly stronger as an *application-facing physical theorem*
than an abstract comparison with two externally supplied Kpt indices:
the old finite index comes from the supplied actual old run, while the
new index/run are constructed from the one new physical original.
The one-sided coverage tests are **conditional** and remain geometric
obligations for the diary construction.

## Why this is not the missing full orbit theorem

The finite coverage tests compare terminal existence and a SET of
complete dependent L+ crossing pairs. They forget multiplicities, exact
parameter identifications, source occurrence positions, all selected
outgoing monoid maps, and which two nodes form an I2 fork. Consequently,
filtered equality of selected I levels does NOT imply equality of
full event-indexed source records, even if the tests pass at every cut.
A common labelled inverse-source monoid orbit still needs separate
normalization and coherent map/parameter transport.

The proof depends on actual old/new numerical structures **already
satisfying** the Henson forbidden-clique avoidance and old-base fidelity
hypotheses. It does not construct an arbitrary safe new column. There is
no ambient-size-uniform bound on the finite indices. The full diary
lower bound and global upper bound are still open.

## Adversarial acceptance checklist

1. The bare seed is `X∪{w}`, not `closure_I(X)∪{w}` and never the full prefix cover.
2. The new root is the ACTUAL physical Kpt original at the prescribed E-free level.
3. A bare physical run exists without an arbitrary inherited parameter set I.
4. An old actual top seed, not merely R.topI, is required to compare scan heights.
5. The cut range is `c<oldTop`, not `c≤newTop`.
6. Old/new live indices are separate finite types, not a fabricated bijection.
7. Both indices enumerate complete meet-and-parameter Kpt closure, not selected graph-age fronts.
8. The full old/upper pair retains auxiliary E and negative atoms.
9. At I2 forks, all crossings are retained; a prescribed single-valued B3 map is inadequate.
10. Comparing terminal *existence* suffices for I1; identity is neither assumed nor inferred.
11. The no-new-pair condition is one-sided NEW→OLD; OLD→NEW is supplied by true source monotonicity.
12. No I3 converse from the ordinary graph-age reduct is used.
13. The new top itself is not removed by source equality; compare selected sets only after restricting to q≤oldTop.
14. Cuts 10/22 of the K4 q2 tests remain candidates for *real* auxiliary events; the finite checks can fail there.
15. The finite check is an assumption, not a conclusion of old-column fidelity or the bare-root constructor.
16. A finite pair-spectrum certificate is NOT equality of labelled inverse fibres or complete event records.
17. No green manuscript validation mark for the BRD characterization, carrier or upper bound.
18. The Lean module must be explicitly imported in its own strict axiom audit and separately built on exact-head CI.

**Lean work plan:** first factor the actual bare-root witness as
`HasPhysicalExhaustiveKptRun`, then derive the conditional two-real-index
old-range selected-set equality from the verified finite comparison theorem.
Use an isolated exact-head workflow plus a separate full project build.
