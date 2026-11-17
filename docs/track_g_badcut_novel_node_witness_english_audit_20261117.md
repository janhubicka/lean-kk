# Track G — intrinsic bad cuts have actual new Kpt node witnesses

**17 November 2026. English-first proof and adversarial audit, before Lean.**

## Why this is not a duplicate

Merged Track E E55 describes bad cuts by the two *Boolean* physical failure flags. Merged Track G #230 identifies the terminal-or-missing-pair reasons for failure **only at old-boring cuts of a genuine old AlgorithmRun**. Track E #203/#204 produces a new-source witness only when the **new AlgorithmRun actually selects** a cut that the old one does not.

The following statement is different and useful for a possible per-stage event budget: **every physical source failure, including one that did not produce a selected new level, has an actual node which is present in the new physical source and absent from the old physical source.** It works for arbitrary physical Kpt source sets at one cut, without a run or nesting assumption. Its crossing clause retains the COMPLETE same-node old/upper dependent L+ ancestors, not just projections to ordinary graph age.

## G1. Physical source-witness normal form

Fix one normalized forbidden family and arbitrary actual Kpt source sets
`Zold, Znew` (they need not be nested). Let c be a source-coordinate cut.
If
`KptPhysicalCutFailure family Zold Znew c`, there exists an actual
Kpt node z satisfying `z∈Znew` and `z∉Zold` and one of:

1. **Terminal:** `lev(z)=c`; or
2. **Complete crossing:** `c<lev(z)` and there exist the real consecutive
   Kpt ancestors `T=ancestor_c(z)` and `U=ancestor_(c+1)(z)` such that
   the COMPLETE pair `(T,U)` is absent from the full physical
   crossing relation of `Zold`.

In case (2) both ancestors come from the SAME z. They include all
negative graph atoms, auxiliary E and dependent parameters, and allow
all I2 forks.

**Proof.** Expand E55's independently verified
`KptPhysicalCutFailure = terminalFailure ∨ crossingFailure`.
For terminal failure, take a genuine new level-c node. If it belonged
to Zold, it would be an old terminal, contradicting the old-terminal
absence conjunct.

For crossing failure, non-inclusion of physical crossing relations
provides a pair `p∈Cross(Znew,c)\Cross(Zold,c)`. Unpack the *definition*
of `FullPhysicalClosureCrossing`: it has a genuine witness z∈Znew
with c<lev(z) and literal raw ancestor equalities at c,c+1. If z
belonged to Zold then the same p would lie in Cross(Zold,c),
contradicting p's absence. Thus z is new-only. The two raw ancestor
equalities and p-not-in-old are the desired stronger certificate.

No source-node bijection, exact finite index, old AlgorithmRun,
mono-map action, no-I2 assumption or selected macrodiary is used.

## G2. Finite intrinsic bad-cut consequence

For the E55 physical bad-cut set on actual source functions
`Zold(c),Znew(c)`, each c∈Bad satisfies c<oldTop, c old-boring,
and `KptPhysicalCutFailure(Zold(c),Znew(c),c)`.
Apply G1 with those two actual pre-cut sources. Hence **every c∈Bad
has a new-only Kpt node witness, at that cut, with the stated
terminal-or-full-crossing alternative.**

This strengthens the previously checked *set of bad cuts* interface
with **real contributing source nodes**, without asserting that the
same witness exists independently of c. In particular it does NOT
produce a single global finite carrier or a matching of selected
endpoint labels.

## Hostile audit / non-implications

1. Do NOT infer from "new-only witness" that at most one bad cut is
   charged to each new node. A single high-level Kpt node has
   consecutive ancestors at many lower cuts. For example, in the
   elementary abstract prefix tree, Zold=∅ and Znew={one node of
   level h}; its crossing relation is nonempty at every c<h, so
   all those cuts are physically nonquiet. This is a logical
   counterexample to the **source-count ⇒ bad-cut-count** inference,
   not a purported example of two genuinely constructed resolved
   Henson AlgorithmRuns. A further per-node bounded *critical
   support* theorem is needed for a diary-uniform budget.
2. "Terminal failure" has an explicit old absence condition; merely
   knowing a new terminal exists is insufficient away from genuinely
   old-boring cuts.
3. A source-node witness for a missing pair has `lev(z)>c`, not
   necessarily `lev(z)=c`. Falsely asserting equality would erase
   auxiliary E crossing microevents and the K4 q2 obstruction.
4. Match complete (T,U) from a SINGLE z. Marginal separate old and
   upper type sets are insufficient, especially at I2 forks.
5. A Kpt node present in Znew\Zold may carry only types already
   present in Zold; it need not cause any bad cut. This theorem is
   necessary-witness, not an iff for arbitrary new-only nodes.
6. Zold,Znew need not be nested. The "new-only" deduction uses the
   literal source-set definitions, not a derived source monotonicity.
7. New-only Kpt source nodes are **not necessarily original Henson
   vertices**: they may be dependent parameters or meet nodes.
   A budget on newly inserted ORIGINAL names is therefore not enough
   without a closure-support/finite-critical-level theorem.
8. For a fixed finite number of new physical source names, the
   possible critical cuts may still increase with the numerical
   height. No uniform per-diary finite bound is claimed.
9. E55's physical bad-cut support is finite because c<oldTop; no
   uniform bound follows as top grows.
10. The K4 physical regression at cuts 10 and 22 with q2=22 and
    selected x=38 remains an essential check on nonselected sources.
11. A cross-occurrence cut reindex map f, bounded Extra, assigned full
    L+ successor types and genuine monoid orbit are still open.
12. The complete corrected-(B3)-loss vs same-old-source relative
    continuation equivalence remains open. This source witness is not it.
13. The independent infinite lower-bound unavoidability theorem is
    not supplied. None of the manuscript's twelve global PENDING
    results can be promoted.

## Acceptance and next constructive target

First formally check G1/G2 under the literal E55/physical-crossing
definitions, with a direct module build, strict parser self-test and
two exact named standard-only transitive axiom reports. Keep source
unmerged and manuscript marks unchanged until those checks pass.

The **substantive next theorem** would show that each new-only
dependent Kpt source node can contribute bad crossings only at a
bounded number of *critical source levels*, computable from a
finite refined-diary event record (rather than from the node's
arbitrarily large numerical height). This is currently only a
research target and could be false without further physical
regularity or closure hypotheses.
