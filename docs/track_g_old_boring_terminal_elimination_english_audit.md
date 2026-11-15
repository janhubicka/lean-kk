# Track G: eliminate redundant terminal matching at old-boring off-plan cuts
**15 November 2026 — English-first proof and hostile audit, before Lean**

## Source-level context

This is **not** a re-proof of the already merged Track E
\`Kk/PhysicalOffPlanFiniteIndex.lean\` (PR #211). That file already provides
the finite-index physical sandwich; the duplicate Track G PR #217 was
closed without merge. Track E PR #220 further studies canonical bad-cut
supports, which are **finite but not diary-uniform**.

The new observation simplifies a *hypothesis* of the verified E52
certificate, rather than duplicating its sandwich result.

## Lemma G1 — terminal exclusion at an old-boring cut

Let \`R\` be a *genuine* AlgorithmRun on a Kpt seed set \`X\`, with
actual top \`t\`. Fix \`c<t\` and assume \`c∉R.I(c)\`.
Then the full pre-cut Kpt parameter closure
\`Z_R(c)=closure_(R.I(c+1))(X)\` contains **no** level-\`c\`
terminal node.

Proof. Suppose there is a terminal node at level \`c\`.
Then \`KptI1AtCut(Z_R(c),c)\` holds. The Kpt definition of
\`IsInterestingAt\` is a disjunction with (I1) as its first
branch, hence \`IsInterestingAt(Z_R(c),c)\` holds. The defining
\`R.interesting_step\` equality says
\`R.I(c)=insert c (R.I(c+1))\`. Thus \`c∈R.I(c)\`,
contradicting old-boringness. No identity of source names,
graph-age approximation, no-(I2), or B3 is required.

## Lemma G2 — exact characterization of terminal *coverage*

At each old-boring off-plan \`c<t\`, let \`oldNode : Fin P → KptNode\`
and \`newNode : Fin Q → KptNode\` with separate live masks.
Assume only **old** exactness: every actual old pre-cut source
node is represented by some old live index and vice versa.

Compare the Track E terminal existence test:

> For every live new node of level \`c\`, there exists a live
> old node of level \`c\`.

with the simpler test:

> **No** live new node has level \`c\`.

They are equivalent. The latter trivially implies the former
because its antecedent is impossible. Conversely, if the old
existence test held and a live new level-\`c\` node existed, it
would supply an old live level-\`c\` node. Old index exactness
places that old node in \`Z_R(c)\`, contradicting Lemma G1.

**Caution:** the stronger no-new-terminal formulation is equivalent
only at cuts **old-boring** for a *genuine* old AlgorithmRun.
It is not equivalent at old-interesting or arbitrary cuts,
and it must not replace the original predicate globally.

## Lemma G3 — simplified complete off-plan finite certificate

Define \`NoNewTerminalOffPlan\` to require, only at
\`c<t\` with \`c∉R.I c\` and \`c∉Allowed\`,
that no live new source index has level \`c\`.
Retain the old Track E **joint** crossing-pair certificate
unchanged: every complete old/upper dependent L+ type pair
of a live new node is realized by **one** old live node.

Under old exactness and genuine old AlgorithmRun assumptions,
\`NoNewTerminalOffPlan ∧ JointPairCoverOffPlan\` is
**if and only if** the existing verified
\`KptTwoIndexOffPlanNoNovelty\` predicate.
Consequently the already merged Track E old-range physical
sandwich can be applied without re-proving it. This gives
an easier *verification target* for each physical induction stage:
a negative no-new-terminal property plus the full paired L+
crossing cover.

This statement does NOT prove these two geometric conditions
for the canonical resolved construction.

## Lemma G4 — intrinsic full physical novelty has exactly two causes

This is a useful *additional* consequence of Lemma G1, independent
of any finite source indexing. Fix a genuine old run R, c<top with
c∉R.I(c), and an arbitrary actual new pre-cut Kpt source Znew.
Let Zold=closure_(R.I(c+1))(X). Then:

  NOT NewRootNoNoveltyAtCut(Zold,Znew,c)
  iff
  (Znew has a level-c (I1) terminal)
  OR
  (some complete dependent old/upper L+ crossing PAIR of Znew
   does not belong to the crossing relation of Zold).

Proof. The definition of NewRootNoNoveltyAtCut is
  (I1(new) → I1(old)) AND (Cross(new) ⊆ Cross(old)).
By G1, I1(old) is false at c. Therefore its first conjunct is
equivalent to NOT I1(new). Negating the conjunction and expanding
non-inclusion of sets yields the displayed two cases. Conversely,
either a new terminal or a new unrepresented complete pair refutes
one conjunct of full physical quietness.

No functionalization of I2 forks, loss of negative L atoms, or
source-name/occurrence transport is used. This is an exact semantic
*disjunction*, not a claim that either obstruction is absent.
With the already verified Track E E54 \`Bad\` membership theorem,
it is the English derivation of the explicit local bad-cut witness
criterion recorded in the current manuscript Track G audit.
Its Lean formalization is a separate proof obligation from G1/G2.

## Hostile audit / rejected shortcuts

1. Ordinary-L old-neighbourhood equality does not imply no new
   dependent Kpt terminals; auxiliary E and parameter closures survive.
2. The no-new-terminal conclusion must be checked on the **pre-cut
   actual closure**, not only on the initial seed set. Track C's
   \`finiteNumericH_rootOnly_lower_initial_I1_iff_old_closure\`
   is insufficient for this.
3. Do not infer terminal absence from a root-only seed having a high
   level: the AlgorithmRun may generate lower dependent parameters.
4. A terminal level-\`c\` witness is an (I1) event even when a
   nonstructural (I3) would otherwise be boring.
5. Old index exactness is required for the backward implication.
   An arbitrary index may omit old terminal witnesses.
6. New index exactness is **not** needed for equivalence of these two
   index predicates, but will be needed when applying E52 to the
   actual physical new pre-cut source.
7. The old and new finite index types need not have the same
   cardinality; no fabricated source-name bijection.
8. At non-boring cuts the original existential terminal-cover
   condition may hold with a genuine old terminal; it cannot be
   replaced by zero new terminals.
9. Leave the full old/upper L+ crossing **pair** condition intact.
   Separate matching of old and upper coordinate projections fails.
10. \`Allowed=Set.univ\` still trivializes the entire off-plan
    criterion; the new equivalence does not solve the need for a
    uniform, transported, occurrence-independent microevent template.
11. The K4 q2 auxiliary cuts (10/22, selected x=38) remain candidates
    for genuine allowed interesting events, not something to delete.
12. This theorem neither constructs an unbounded resolved H+ nor
    proves the corrected-(B3)-relative continuation bridge, a
    common labelled source orbit, or any infinite lower bound.

## Lean acceptance

Implement and check **two declarations**:
(1) old-boring actual Kpt pre-cut closures have no terminal at that cut;
(2) an iff between the verified E52 finite off-plan predicate and
the simplified no-new-terminal-plus-joint-pair predicate, under
genuine old Run + old index exactness.

Import the **existing** Track E E52 module rather than duplicating
its definitions. Run exact-head targeted build and the full
central named transitive-axiom parser gate; keep all 12 manuscript
global pending results pending. Do not repin manuscript validation
to an untested PR.
