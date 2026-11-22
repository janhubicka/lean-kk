# Nonedge big Ramsey degree: proof audit, 22 November 2026

## Verdict and source snapshot

The candidate **24** is a finite history count. The audited sources do not
yet prove that the unordered nonedge has big Ramsey degree 24. They
contain substantial local theorems for a lower-bound construction and
for an upper-bound construction, but neither construction has been
composed into the required infinite coloring theorem.

This is not a counterexample to 24. It is a precise distinction between
an enumerated candidate and a proved degree. In particular, a historical
claim that the manuscript already contained a complete independent
English upper-bound proof is not supported by the current manuscript.

Sources inspected:

- `lean-kk` main at `a900c510196ce3e1d7551ebb11e2eaaf6da3481a`.
- `Counting-big-Ramsey-degrees-of-K_k-free-graphs/kk.tex`, Git blob
  `3bc9334ff2f9db1b5f3e36aeb12f1db93e33ff37`, especially Appendix
  `App:Direct_Independent_Small`.
- The local semantics/count modules being developed alongside this audit
  are new work, not results already present at the preceding commit.

This note is an adversarial source audit. It does not report a fresh
successful compilation of every imported historical module. The build
and axiom reports for the new formalization must be read separately.

## 1. The actual theorem and the two obligations

Let `G` be a countable universal homogeneous simple `K₄`-free graph.
An unordered nonedge copy is a two-element vertex set with no edge.
The desired upper assertion is

> For every finite coloring of all unordered nonedges of `G`, there is
> an induced self-embedding of `G` on whose range at most 24 colors occur.

The desired lower assertion can be witnessed by

> One coloring of the unordered nonedges with 24 colors such that every
> induced self-copy realizes all 24 colors.

The new `Kk.NonedgeBRD` interface makes these separate obligations
explicit: `DegreeLE G 24` and a coloring to `Fin 24` satisfying
`Unavoidable`. The generic theorem `degreeEq_of_upper_and_unavoidable`
combines them into `DegreeEq G 24`. Neither a finite cardinality
calculation nor a conditional theorem assuming these obligations is an
unconditional proof of the degree.

There are two distinct label conventions. A nonedge has two ordered
embeddings per unordered image. A finite history already records the
temporal/lexicographic choices relevant to an unordered image; adding
labels to its two terminal vertices is a further factor of two. The
candidate copy degree is 24; the corresponding candidate embedding
degree is 48. The intended theorem must therefore use unordered copies.

## 2. What the finite number counts

The proposed independent-pair histories start with one sort of
singleton age 3. They contain exactly one split, exactly two independent
zero-code events, and intervening downward covers in the poset of
canonical age functions.

After the unique split the three possible canonical pair states, written
as `(F({0}), F({1}), F({0,1}))`, are

| Singleton age when split occurs | Pair state after split | Proposed completions |
|---|---|---:|
| 3 | `(3,2,3)` | 16 |
| 2 | `(2,2,2)` | 6 |
| 1 | `(1,1,1)` | 2 |

The candidate total is `16 + 6 + 2 = 24`. Each initial descent before the
split is forced, so it introduces no additional multiplicity.

The important invariant is the **canonical entire sorted graph age**,
not the raw common-neighbor table. For actual old-neighbor sets `U_i`,
the raw support capacity is

`b(S) = 3 - omega(intersection (i in S), U_i)`.

One then takes the feasible integer clique multiplicities satisfying
every support inequality, and canonicalizes by maximizing the mass on
each support. Different raw tables may define the same canonical age.

For example, the manuscript correctly notes that changing only the raw
singleton bound of sort `i` from 2 to 1 in the raw table `(2,1,3)` leaves
the raw pair bound 3 unchanged but changes the canonical pair bound from
3 to 2. A calculation which silently treats a raw singleton change as
leaving all canonical mixed supports fixed would count the wrong object.

The independent code law is also stronger than singleton age 1: the
coded sort `j` must satisfy `F(S union {j}) = F(S)` for every nonempty
surviving support `S`, and every surviving passing bit must be zero.
Counting deletions justified only by `F({j}) = 1` is insufficient.

## 3. Lower bound: substantial components, no history theorem yet

### Strongest relevant existing interfaces

`TrackFK4CompleteTupleSynchronization.lean` contains
`k4_sync_complete_tuple_canonical_class`. Its inputs include distinct
same-level actual source one-types, an arbitrary injective induced
source-to-target graph map, equal source/target ranks, and recursively
rank-large **actual coding-node fibers**. Its outputs include one common
target level beyond a prescribed bound, compatible refinements,
injective target types, private source markers, preservation of every
source raw support, and equivalence of all finite sorted `K₄`-free graph
tests. The induced map need not preserve the original enumerations.

The current checkout also contains the newer
`TrackFPhysicalNumericAgeFromClasses.lean`:

- `trackFPhysical_numeric_age_eq_of_full_K4_tests` recovers literal
  numeric canonical age equality from the universal sorted graph tests.
- `k4_sync_complete_tuple_numeric_canonical_age` obtains that equality
  for the actual synchronized fronts.
- `k4_survivor_sync_numeric_canonical_age_after_code` obtains it for
  surviving fronts after an independent code.

These are stronger than pairwise or singleton compatibility. In
particular, all mixed supports and repeated sort labels in a finite
clique are included. The latest main has this numeric endpoint component
even though the inspected manuscript still describes its PR as under CI.

The code event also has genuine local ingredients:

- `sourceCodingFibre_rank_zero_independent_code` in
  `TrackFActualIndependentCode.lean` chooses an actual independent coding
  vertex beyond finite source/target bounds.
- `k4_survivor_sync_after_zero_code` in
  `TrackFZeroCodeSurvivorSynchronization.lean` constructs simultaneous
  later survivor fronts with zero at the chosen target code.
- `TrackFActualPrecodeTargetFront.lean` constructs the genuine precode
  target front.
- `trackFActualFront_full_precode_age_eq_of_zero_code_endpoints` in
  `TrackFPrecodeEndpointAgeSandwich.lean` proves full precode age rigidity
  from endpoint equalities.
- `TrackFPhysicalSurvivorDeletion.lean` addresses actual physical
  deletion and sort reindexing.

Track B additionally has
`henson_leftDense_constructs_finite_physical_cover_history` in
`FinitePhysicalCoverHistory.lean`: it constructs a finite chronological
cover history in one actual graph under its stated hypotheses. That is
not the target history occurrence theorem in every induced copy, and it
does not include the complete split/code schedule.

### Remaining lower theorem, specialized to two vertices

The focused missing statement is:

> For every one of the 24 legal independent-pair histories and every
> induced self-embedding `e` of the chosen Henson graph, there are two
> distinct nonadjacent source vertices whose image pair has exactly that
> selected age/meet/code record, with no additional selected event.

It requires a single chronological invariant, not just unrelated
endpoint equalities. That invariant must retain full canonical age,
compatibility with genuine target coding fibers, zero incidence to all
already coded selected vertices, the actual target order of the active
sorts, and the event record accumulated so far.

The one split must be shown to be the unique selected target meet, with
the correct full pre/post ages. Each cover must occur once with no
hidden selected event. The two code events must use the actual target
enumeration order and actual survivor reindexing. Finally, the record
function on **every** unordered nonedge must be defined, noncanonical
records assigned a legitimate default color, and the realization
theorem applied to prove all 24 colors unavoidable.

The English lower argument sketches how these pieces should fit. This
audit found no specific counterexample to that argument, but the current
Lean statements do not supply the required induction or record theorem.
Thus they cannot presently be composed into the advertised lower bound
without additional proof.

### Enumeration hypothesis must remain visible

The actual source coding density and several physical realizations use
`OnePointLeftDense`. This means that an admissible one-point extension of
an old initial segment can be realized later with no positive edges to
the intervening vertices. It is stronger than the ordinary one-point
extension property for a fixed arbitrary enumeration.

The manuscript stipulates a left-dense enumeration. The existing
`HensonLeftDensityBridge.lean` explicitly does not construct one from
Fraisse amalgamation. A final theorem for `IsHenson4` must therefore
construct/re-enumerate a suitable model and transport BRD by induced
isomorphism, or derive the needed source construction by another route.
K₄-freeness alone does not imply any density property.

New work accompanying this audit now discharges this ambient-model
issue: `HensonLeftDenseConstruction.lean` constructs a concrete
clique-free left-dense presentation, and `HensonUniversality.lean`
derives induced universality from the ordinary extension property and
model-independence of the degree predicates. These additions do not
discharge the actual-history induction.

There is also a deliberate rank shift: the manuscript singleton ages
are 1, 2, 3, while `HensonOneType.rank` is zero-based, hence 0, 1, 2.
The code condition at manuscript rank 1 is a rank-zero condition in
these Track F modules. This shift is documented in the existing source.

## 4. Upper bound: current manuscript explicitly leaves the key lemma open

The manuscript proposition `prop:small-independent-upper` states an
unconditional bound by the number of histories. Its proof passes through
the following dependency chain:

1. Construct the resolved ordinary graph `Q` and an induced Henson copy.
2. For each selected independent set, retain its structural/age blocks
   and prescribed numerical generation/free levels, forming a set `I`.
3. Prove `lem:small-independent-full-boring`: every level outside `I`
   can be skipped on the **full** parameter-closed Kpt source.
4. Use this to prove `lem:small-independent-common-full-source`: all
   occurrences of one history are images of one finite complete source
   under the genuine normalized monoid.
5. Apply the finite source-orbit Ramsey theorem and transfer to a copy.

Step 3 is not established by the current proof. It explicitly says that
the descending stage-pool inclusion and marked chosen-type comparison
are still open. Its closing paragraph says that full one-level
boringness would follow provided the actual stage inclusion, all
structural I1/I2 exclusions, and the chosen marked corrected-B3 test are
established, and says these hypotheses remain unproved for the proposed
`Q`. Step 4 begins by applying this very lemma.

Consequently the unconditional statement of the proposition is stronger
than the completed argument. Formalizing the assertion with one of
these missing facts as a hypothesis would yield a conditional upper
bound, not a proof of `DegreeLE G 24`.

### The exact remaining local gate

The strongest relevant general lower-real-cut interface is

`henson_actualRun_lower_real_unselected_of_planned_stage_markedB3`

in `TrackDPlannedStageRoles.lean`. It concerns the true source at
`Run.I(cut + 1)`, not an assumed final pool. Its hypotheses include:

- genuine finite numerical Henson graph and actual AlgorithmRun;
- a positive lower-generation real cut below the source height;
- the descending inclusion `Run.I(cut + 1) subset Plan`;
- actual chronological `ResolvedQChronologicalAxioms` and the retained
  physical-role shape, including a dummy cap and retained whole blocks;
- no complete-source I1 endpoint at this cut;
- no complete-source I2 competing meet at this cut;
- corrected B3 for the actual chosen marked source.

The marked predicate is genuinely represented in the current full
closure and has selected top-coding physical role. The theorem proves
positive full physical name coverage from the role hypotheses. Thus that
coverage is not an additional arbitrary axiom. However, the three final
structural/age tests are still inputs, not consequences of a selected
age table.

The focused n=2 goal is to discharge these remaining tests for **every
omitted auxiliary or nonselected-coded base**, under the true descending
stage assumption, using the actual resolved construction. Then complete
the descending induction and the common finite-source comparison. The
root/cap source and all directed auxiliary E atoms must remain fixed
through this argument.

### Cases that really have been reduced further

Recent results mean that it would be inaccurate to call every case
equally open:

- `henson_topSeeds_odd_omitted_of_closed_plan` in
  `TrackDOddTopSeedPlanSkip.lean` handles odd cuts from actual top-cap
  seeds, closed planned free cuts, and the descending hypothesis.
- `henson_topSeeds_isolated_dummy_lower_real_skip` in
  `TrackDTopSeedConcreteLowerSkip.lean` handles isolated dummy lower-real
  cuts without a planned-stage hypothesis.
- `henson_topSeeds_selected_coded_lower_real_skip` in the same file
  handles lower copies of selected independent coding bases under the
  descending role hypothesis.

These concrete theorems derive their full I1/I2/B3 exclusions; they do
not merely assume them. The unsolved positive-cut cases at omitted
auxiliary/nonselected-coded bases are therefore the sharper target.

## 5. Why two selected vertices do not automatically solve B3

A corrected B3 test quantifies over arbitrary finite continuations
using the allowed upper **types**. An allowed type may be used more
than once. Two selected graph vertices therefore do not limit the
continuation to two future vertices, nor remove mixed old/future K₄
obstructions.

The repository contains two particularly useful regression examples:

1. `fourCliqueCore_singleUpper_B3_fails` in
   `K4SingleUpperB3Core.lean` uses two future copies of **one** complete
   upper L-type over an adjacent two-vertex old socle. Restoring one old
   vertex creates K₄, although deleting it leaves a permitted graph.
2. `k4Gadget_cut10_x_only_B3_good` in
   `K4Cut10SelectedOnlyB3.lean` proves that the selected x-only test at
   literal numerical cut 10 passes. Nevertheless
   `k4Gadget_algorithmRun_selects_cut10` in
   `K4ActualAlgorithmRunCut10.lean` shows that the full actual source
   retains cut 10 because its parameter closure contains an additional
   auxiliary original type.

These are concrete counterexamples to shortcuts based on a small
selected shadow. They are **not** counterexamples to the strengthened
resolved-Q plan or to the numerical candidate 24. The current planned
stage-role theorem was designed to avoid precisely this illicit
projection. Its hypotheses still have to be instantiated.

## 6. Safe conclusion and next proof target

The finite 24-history calculation and the ordinary graph/BRD semantic
bridges are worthwhile standalone formalization goals. They address two
real sources of past errors: incorrect transition/counting rules and
incorrect interpretation of the mathematical invariant.

They should be reported with the following boundary:

| Claim | Status established by this source audit |
|---|---|
| The proposed independent-pair history automaton has 24 histories | Separate finite kernel check is being supplied; no infinite consequence by itself |
| The existing normalization intends simple K₄-free graphs | Supported by the loop/asymmetry/clique forbidden signature; new semantic equivalence supplies an explicit bridge |
| The desired BRD is for unordered nonedge copies | The new explicit finite-set copy interface fixes this convention |
| All 24 histories occur in every induced Henson self-copy | Not yet an existing complete Lean theorem |
| A 24-source family canonizes all finite nonedge colorings | Not yet an existing complete Lean theorem; current English full-boring proof explicitly remains open |
| Unordered nonedge BRD equals 24 | Not proved by the audited sources |

A focused lower proof should finish the actual two-terminal event
induction and its unavoidable-coloring map. A focused upper proof should
start with the positive omitted auxiliary/nonselected-coded cuts under
the exact stage role invariant, then prove the common complete source
for each of the 24 records. No JEMS exactness theorem or general diary
identification is needed as an input to formulate either task.

## 7. Independent review of the new semantics and finite-count modules

After the initial audit, both new modules were inspected independently
of their authors. This is a mathematical definition review; compiler
results remain the separate integration gate.

### `NonedgeBRDSemantics.lean`

No logical defect was found in the proposed definitions or transport
interfaces:

- `NonedgeCopy` is a finite **set** of cardinality two. Swapping its
  endpoints gives the same copy. It contains no enumeration or labeling
  parameter that could inadvertently double the counted objects.
- `SimpleGraph` supplies irreflexivity and symmetry. The normalized
  signature bridge explicitly deals with loop, both directed asymmetry,
  and clique obstructions, and identifies clique exclusion with
  `SimpleGraph.CliqueFree` using increasing enumerations of finite sets.
- `HensonExtension` requests every finite disjoint positive/negative
  adjacency pattern whose positive set is triangle-free, with the new
  vertex outside both sets. It is not defined to include a desired BRD
  value, a diary theorem, or a left-density assumption.
- `DegreeLE` universally quantifies the number of colors and the entire
  coloring before existentially choosing the induced self-copy and its
  palette. Its embedding preserves and reflects adjacency and need not
  preserve the order on `Nat`.
- `exists_map_iff_inRange`, `degreeLE_iff_onRanges`, and
  `degreeLE_iff_onSubcopies` verify that using preimage copies does not
  accidentally omit some unordered nonedges inside the chosen range.
- `DegreeEq` is a least-bound condition, and `Unavoidable` demands
  surjectivity in every induced self-copy. The exactness theorem's upper
  and lower premises are explicit; it is not a theorem asserting a
  numeric answer from the definitions.
- Quantification over `Fin 0` is harmless: when nonedge copies exist
  there is no coloring into `Fin 0`. The extension property separately
  proves existence of a nonedge, so the intended Henson application has
  a nonempty copy domain.
- `degreeLE_of_mutual_embeddings` uses the valid composition
  `H -> G -> G -> H` to transport a coloring bound. Its isomorphism
  corollaries legitimately remove dependence on the chosen enumeration.

`IsHenson4` is the standard countable extension-property presentation.
The new semantic module does not itself prove the back-and-forth
uniqueness theorem for that presentation. The separate left-dense model
construction now establishes nonvacuity concretely: a fair schedule
tries every finite neighbor set cofinally, adds a vertex only when its
neighbor set is triangle-free, and preserves all older edges. A final
safe finite set is safe at its scheduled stage by this stabilization,
so the full prescribed old column and intervening zeros are realized.
The new ordinary-extension universality theorem gives induced embeddings
between all `IsHenson4` models in both directions. This is sufficient for
degree invariance, without a back-and-forth isomorphism theorem. Both
actual source files were independently reviewed and no mathematical
defect was found; their successful compilation was observed by their
owning agents.

### `NonedgeHistoryCount.lean`

No overcount, undercount, or incorrect local transition was found in the
machine under its stated interpretation:

- Canonical capacities are derived from attainment by integer weight
  pairs, not supplied as a list of 13 accepted triples.
- Covers are tested against **all** 27 bounded triples and all 13 valid
  profiles, rather than just the reachable states.
- The split feasibility theorem exactly states
  `x + y <= r` and `y <= 2`, including the compulsory right-child drop
  when the parent capacity is three.
- A left code requires `a = 1` and `c = b`; a right code requires
  `b = 1` and `c = a`. At `(1,1,1)` both are allowed and remain
  different event lists, correctly retaining the two coding orders.
- The phase distinction forces one split before the two codes. Omitting
  a unary code before the split removes only a dead path: an empty
  active front cannot later split to produce two coded vertices.
- Every accepted list has a proved measure bound. Membership in the
  finite enumerator is equivalent to the unbounded recursive acceptance
  predicate at that bound. The number 24 is not built into the state
  definition or used as a fuel bound.

A separate computational check represented each age by its **set of
feasible integer weight pairs**, ordered these sets by actual inclusion,
derived covers from that set order, and applied the code law. It again
obtained 13 classes, and continuation counts 16, 6, 2. This is independent
evidence for the finite calculation, not a replacement for Lean's
kernel check.

The local equivalence between coordinate order and feasible-class
inclusion is now proved in the counting module. The additional
`NonedgeProfileBridge.lean` closes its connection to the repository's
general `IsIntegerGraphAge`; details follow below. The connection to
actual selected graph-age records remains open. An abstract canonical
profile need not be an actual **distinct** two-type front. For example
`(3,3,3)` has two
capacity-three sorts, both with empty old-neighbor set; they would be
the same actual one-type. This profile is unreachable from the three
split states and is harmless as an ambient poset element. The count of
13 must therefore be described as abstract canonical profiles, not 13
actual distinct-front configurations.

The new files make the finite calculation and the degree's meaning
reviewable. Their faithful local definitions do not supply the missing
infinite unavoidability or common-source canonization theorem.

## 8. The generic age-representation gap has now been closed

`Kk/NonedgeProfileBridge.lean` maps the finite history triples to the
existing `IntegerGraphSupport 2 4 -> Nat` functions. It handles the three
nonempty supports explicitly and gives empty support value zero. Its
`all_support_feasibility` and `feasible_iff_existing_weights` theorems
show that the elementary inequalities are exactly the generic integer
weight constraints, with no loss caused by the normalized total bound.
The latter bound follows from feasibility itself.

`toAge_is_age_iff` proves equivalence of the triple saturation predicate
with the repository's actual `IsIntegerGraphAge 2 4`. The converse
representation `exists_unique_profile` covers **every** generic
two-sort canonical age function. Consequently `covers_iff_ageCover`
compares covers against all generic intermediate ages, not merely a
selected list or reachable profiles. `canonical_fixed` uses the
existing generic canonicalizer's greatest-age and raw-bound properties.

The new file compiled with pinned Lean 4.35.0-rc3. Ten principal theorem
axiom reports contained only `propext`, `Classical.choice`, and
`Quot.sound`. The finite count is therefore connected to the existing
finite age formalization rather than a disconnected alternative
definition. This does not identify histories with actual coding-tree
events or complete successor-tree source orbits.
