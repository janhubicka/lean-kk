# Track A/G — full-source selected-level localization outside a finite exception set

21 November 2026. English proof and adversarial audit BEFORE Lean implementation.
This is a conditional finite successor-tree reduction. It does **not**
establish that ordinary binary-L age equality controls dependent Kpt events.

## The statement

Let `S` be an actual successor tree with monoid `H`. Let `X,Y`
be arbitrary, possibly different seed sets, and let `RX`, `RY`
be genuine `SMTree.Envelope.AlgorithmRun` structures at one aligned
natural-number scan top `N`. Fix *any* exceptional set
`C : Set Nat`, not necessarily finite.

For `i<N`, write `D_X(i)` for the genuine
`IsInterestingAt H (closure S (RX.I (i+1)) X) i` decision,
and `D_Y(i)` for the analogous decision in the actual `RY` tail.

Assume

    for all i<N outside C: D_X(i) iff D_Y(i).

Then for **all** stages `s<=N` and **all** levels `j` outside `C`,

    j in RX.I(s) iff j in RY.I(s).

In particular, the symmetric difference of the final selected
sets `RX.I(0)` and `RY.I(0)` lies inside `C`.
If `C` is finite, its cardinality bounds the number of
disagreeing selected levels; this does not bound either selected
set itself, and does not imply equality inside `C`.

## Proof: actual backward recursion

Use strong induction on `N-s`. At `s=N`, both selected sets are
empty by the actual `AlgorithmRun.topI` field.
For `s<N`, the induction hypothesis gives membership agreement
outside C at stage s+1. Fix `j\notin C`.

- If `s\in C`, then `j\neq s`. The AlgorithmRun step at `s`
  either inserts `s` or leaves the next selected set unchanged
  in *each run independently*. Inserting an element different
  from `j` cannot change membership of `j`; therefore both
  current memberships equal their corresponding stage-(s+1)
  memberships and hence agree.
- If `s\notin C`, the hypothesis equates the two genuine
  interestingness decisions at precisely their actual
  stage-(s+1) parameter closures. Both runs consequently
  perform the same set operation (insert s or identity), and
  equality of memberships outside C follows from the
  induction hypothesis.

This proof does NOT need equality of seed sets, source-node
indices, monoid factors or the stages' complete selected sets.
The exceptional steps can affect future pre-cut closures, but the
premise compares the **actual** resulting decisions at every
remaining nonexceptional step.

## Dependent Kpt specialization

Fix a single normalized forbidden-pattern family and two genuine
Kpt AlgorithmRuns at the SAME scan top. Let their actual pre-cut
closures be

    Z_i = closure (RX.I (i+1)) X,
    W_i = closure (RY.I (i+1)) Y.

Suppose for every `i<N` outside `C`:

1. `KptI1AtCut family Z_i i` iff
   `KptI1AtCut family W_i i`;
2. `FullPhysicalClosureCrossing family Z_i i =
    FullPhysicalClosureCrossing family W_i i`.

The already merged (independently tested) Track G theorem
`kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq`
gives `D_X(i) iff D_Y(i)`, including I2 and I3.
The generic result now establishes selected-set agreement
outside C at **every** stage.

Note that no equality of ordinary binary-L ages is required in
this *conditional* theorem; no conjectural implication from L
to the full dependent L+/E crossing relation has been used.

## Track A specialization and precise gap

For the finite ordinary critical-generation schedule of PR #351,

    C = C(E,b,j) = {p_U : U nonempty, b U-eligible, c_U=p_U},

genuine K_ell-freeness implies `|C|<=ell-2` in English (and
the source proof is pending kernel verification). Instantiating the
generic Kpt result with this C would conditionally bound the
number of **disagreements between two selected scans**
by `ell-2` whenever the two complete Kpt terminal and crossing
profiles agree outside C.

This is NOT an upper bound on the total number of interesting cuts:
both scans may select arbitrarily many of the SAME auxiliary
interesting levels. Nor does the Track A raw schedule by itself
imply either of the required Kpt profile equalities.

The important remaining nonconditional theorem is exactly:

    diary data  => complete terminal and full L+/E
                   crossing-profile match at all cuts outside C,

including true parameter-closure indexing, not just selected
ordinary-L shadows. This implication is currently OPEN.

## Adversarial checks

1. Both runs must have the same numerical top; no cross-height
   reindexing is silently inferred.
2. The exceptional set need not be finite for the set inclusion;
   finite cardinality is invoked only afterward.
3. Even if a cut belongs to C, its different insert/no-insert
   choices cannot change membership at any different level in
   the same recursion step. They can, however, affect all
   *subsequent* true pre-cut interestingness tests.
4. Thus the assumption uses the true closures
   `RX.I(i+1), RY.I(i+1)` of the potentially different runs.
   It cannot be replaced with matching tests on one common
   fictitious selected tail.
5. For i outside C, equality of decisions is exactly the
   hypothesis needed to apply both AlgorithmRun's
   `interesting_step` or `noninteresting_step` at i.
6. The Kpt crossing relation must preserve ALL dependent
   old/upper L+/E atoms, not its ordinary-L projection.
7. The I1 terminal flag is independent of crossing pairs and
   cannot be dropped.
8. Forks (I2) and skip obstructions (I3) are handled by Track G's
   full-source comparison; no unjustified source bijection
   or two-way coherent map is imposed.
9. Equality of ordinary ages does not assert the required
   complete Kpt profile match; PR #351's raw/canonical event
   schedule is only the proposed exception set.
10. The output is an inclusion for SELECTED-LEVEL DISAGREEMENTS,
    not a labelled inverse-source orbit, full Ramsey upper
    bound, or exact BRD computation.
11. A zero-top scan is covered: the run's top selected set is
    empty and the result is vacuous.
12. The result should be formally audited for standard-only
    transitive axioms; a submitted proof body is not verification.

## Lean acceptance

Implement a generic theorem in a fresh standalone module importing
`Kk.TrackGDistinctSeedProfileScan`, then a Kpt specialization by
applying the already checked full terminal+crossing interestingness
criterion. Add a separate strict fully qualified `#check` /
`#print axioms` gate with an exact-head CI workflow. The
PR #351 sharp critical-generation source can be connected only
once its own Lean kernel gate passes; do not introduce a hidden
dependency on the unverified branch. Do not change frozen black
manuscript text.
