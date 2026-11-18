# Track G — full local Kpt event profile determines Algorithm 5.4 interestingness

18 November 2026. English proof first. Deliberately compare DIFFERENT
physical Kpt source sets at the SAME raw numerical cut in ONE fixed
normalized forbidden-family successor tree. No common node carrier
or literal source inclusion is assumed.

## Main improvement

Let Z,W be arbitrary sets of admissible Kpt nodes, cut c fixed.
The complete local event data consist of:
(T) terminal-existence flag: some z in the actual full source
    has level exactly c (genuine I1), and
(C) the full relation of complete dependent raw L+/E ancestor
    pairs (z|c, z|(c+1)) of ALL source nodes extending c.
Keep entire negative L bits, E bits and dependent parameters.

**Theorem.** If the terminal flags agree and the two complete
physical crossing relations are EQUAL as sets of raw Kpt pairs
at c, then

  IsInterestingAt(normalizedKptSMTree, Z, c)
    iff IsInterestingAt(normalizedKptSMTree, W, c).

This includes the genuine I3 skip-map obstruction, not just I1/I2.
The index sets may have different cardinalities, and Z,W need not
share a literal Kpt node. No I2-free or E1 assumption.

## Lemma 1: a crossing pair has a real node mate

Suppose the two full crossing relations at c are equal.
For any z∈Z with lev(z)>c, its ancestor pair is in the
full physical crossing relation of Z. By equality it has
a witness w∈W with the SAME raw old and upper Kpt type nodes.
The verified `kpt_actual_crossing_has_physical_full_pair`
provides the complete raw L+/E types of z; the witness
in W supplies their physical realization. Since the
admissible Kpt node type is a subtype of raw partial-type
nodes, equal raw old/upper records imply literal equality
of both admissible ancestors (subtype extensionality).
Thus w may be different from z, but

  ancestor(z,c)=ancestor(w,c),
  ancestor(z,c+1)=ancestor(w,c+1).

This is a per-cut ancestor-pair comparison between different
actual sources. There is no global per-node bijection, and
the choice of w need not be consistent at adjacent cuts.

## Lemma 2: the complete skip constraint depends only on (C)

Fix any total genuine monoid map D:MMap H. The condition

  for all z∈Z crossing c,
    D(ancestor(z,c)) = ancestor(z,c+1)

is equivalent to the identical condition for W.
Indeed take each w∈W crossing c and use Lemma 1 in the
reverse direction to find z∈Z with the same actual pair.
The equation for z then gives exactly the equation for w.
The reverse implication is symmetric. The `SkipsOnly c`
property depends only on D and c, so the existence or
nonexistence of a one-level skipping D satisfying the whole
source constraint is the SAME in Z and W. This is precisely
the I3 part of the genuine algorithm's trichotomy.

## Lemma 3: I1/I2 alternatives depend only on (T,C)

The verified unconditional identity
`kpt_I1_or_I2_iff_I1_or_physical_nonfunctional` states
that a genuine I1 OR I2 obstruction is equivalent to:
terminal existence OR nonfunctionality of the complete
physical crossing relation (two distinct U,V over one
old raw L+/E type T). Terminal equality and relation
equality therefore equate the structural alternatives.
Note the exact I2 predicate alone may be confounded with
a terminal self-meet, but the I1 OR I2 form is unconditional.

## Main theorem proof

`IsInterestingAt` is the disjunction of I1, I2 and the
absence of a genuine skipping MMap satisfying all source
crossings. Lemma 3 identifies I1 OR I2; Lemma 2 identifies
the entire I3 obstruction. Thus their disjunctions agree.
No simplified graph-age or selected-front proxy is used.

## Finite index / cross-occurrence application

Let Z and W have separately exhaustive complete physical Kpt
source indices `nodeP/liveP`, `nodeQ/liveQ` at cut c;
their finite name types may be unrelated (and need not even
have equal sizes). If their indexed terminal-existence
predicates agree and their `IndexedPhysicalCrossing`
relations agree, then their actual local `IsInterestingAt`
predicates agree. Proof: verified
`physical_I1_I2_iff_indexed_active_nodes` recovers the
terminal flags, and
`indexed_physical_crossing_eq_full_closure_relation`
recovers the full physical relations. Apply the main theorem.

The matching finite profiles are not yet derived from
equality of the **selected macrodiary** or from prescribed
numerical-H+ schedule. This application is the proper local
target for cross-occurrence validation: finite actual full
source signatures suffice, without postulating any source
node bijection. One may use verified Track E two-sided
pair-matching to establish crossing equality, but terminal
flags MUST be checked independently.

## Adversarial audit

1. FULL Kpt L+/E pairs, not ordinary L-reduct pairs, must match.
2. Matching unlabelled upper spectra without their paired OLD
   types is insufficient for the skip-map constraints.
3. Only one numerical cut c is aligned; the theorem does NOT
   construct chronological cut-coordinate reindexing.
4. Equal full crossing relations do NOT imply terminal equality:
   a level-c terminal contributes no crossing above c.
5. The I1/I2 statement uses the unconditional DISJUNCTION;
   it does not claim the I2 predicate itself is determined
   without knowing I1 and handling trivial self-meets.
6. The full crossing relation includes all competing I2 fork
   choices; no functionality assumption is made.
7. Each pair has a SAME-NODE witness within its own source;
   matching just the two marginal sets would be too weak.
8. A W witness for a Z crossing can be different from z, and
   several Z nodes can be represented by one W node at c.
9. Equal raw Kpt ancestor nodes imply equality of admissible
   ancestor nodes by subtype extensionality, not graph isomorphism.
10. A skipping monoid map is tested on all complete crossing
    constraints, not on only selected terminal graph ages.
11. The same D is used when transferring a skip constraint;
    hence existential/nonexistential I3 decisions transport.
12. Equality of local I3 decisions does NOT identify the
    arbitrary skip-only maps chosen by two real runs.
13. No assumption about source-set equality, inclusion, or
    equal finite source cardinality is introduced.
14. This theorem is for the SAME normalized family/tree.
    Across different families an additional structural map
    compatible with the monoid would be necessary.
15. A finite index must be EXACT on the entire actual
    parameter-closed pre-cut source, not a selected L shadow.
16. The verified K4 auxiliary selected cuts 10/22 are not
    discarded: their genuine local event signatures detect them.
17. Uniform finite labelled event budget and absence of
    unrecorded microlevels do not follow from this one-cut test.
18. The infinite resolved copy and all different-occurrence
    source-profile equalities remain unproved.
19. The global labelled inverse-source monoid orbit and exact
    big Ramsey degree characterization remain open.
20. No lower-colouring unavoidability follows from the
    local comparison theorem.

## Lean acceptance

Import the real `NumericHPhysicalI2Fork`,
`IndexedPhysicalStructuralEvents`, `IndexedPhysicalCrossing`
and actual `SuccessorTree.Envelope` trichotomy. Prove:
(1) physical pair-mate equality of actual Kpt ancestors;
(2) skip law equivalence for every real MMap;
(3) full IsInterestingAt equivalence from terminal+crossing;
(4) application from independent exact indexed source signatures.
Commit English first; then build the exact standalone module
and strict FOUR qualified standard-only named axiom reports.
Use independent full Lean CI and inspect the actual source
before marking only narrowly scoped BLUE manuscript text.
