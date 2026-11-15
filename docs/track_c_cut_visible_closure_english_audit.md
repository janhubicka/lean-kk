# Track C: Cut-visible closure and nonvacuous full-source absorption

**15 November 2026. English-first proof and hostile mathematical audit; read before formalization.**

## Problem exposed by the previous C proof

For an old genuine AlgorithmRun on X with selected final levels I=Rold.I0 and a new run on
Yfull=closure_I(X)∪O, old C's pre-cut absorption asserted full equality
closure_J(Yfull)=closure_J(X∪O) only if ALL q∈I lie above the cut c. This can be vacuous
if 0∈I; even when it is not, previously selected q≤c are genuine. PR #218 resolved
nonvacuous *retention* of every old q>c in the new pre-cut level set
J=Rnew.I(c+1). But full equality of closure sets is still unproved.

There is a stronger repair **visible at the cut**: lower inherited parameter
generations cannot produce a node at or above c. Thus complete closure equality
is unnecessary. We can prove *exact equality of the cut-visible closure* and hence
I1/I2 and complete dependent L+ crossing, without assuming ALL old q>c.

## Essential grading fact

For a successor representation at base level i of node a, every actual parameter
x in its parameter list satisfies lev(x)<i. This is the upstream
\`STree.parameter_level_lt\` axiom. Meets satisfy
lev(meet(a,b))≤min(lev(a),lev(b)). Both operations **strictly decrease or preserve**
height, and a parameter produced at an index i≤c lies **strictly BELOW** c.

Set Low(c)={z:lev(z)<c}; for any set C that is meet-closed and parameter-closed
over J, and any I such that every i∈I with i>c also lies in J, the union
W=C∪Low(c) is meet-closed and parameter-closed over I:

- Meeting two points of C stays in C. If at least one is in Low(c), its
  meet has level <c.
- Consider a selected parameter operation at index i on a∈W. If i≤c,
  each parameter x has lev(x)<i≤c, hence x∈Low(c).
- If i>c, a cannot be in Low(c), because i<lev(a). Hence a∈C and
  i∈J, so x∈C.

This argument handles the boundary i=c exactly: its parameter nodes have
height <c and cannot create an I1 source *at* c.

## Generic theorem A: high-level closure monotonicity

For seed sets X⊆Y and sets of selected parameter levels I,J, assume
∀ i∈I, c<i → i∈J. Then every z∈closure_I X with c≤lev(z) lies in
closure_J Y.

**Proof.** Take C=closure_J Y and W=C∪Low(c). W contains X and is
meet-closed and parameter-closed over I by the preceding graded argument.
The minimality of closure gives closure_I X⊆W. A member z of level≥c
cannot be in Low(c), so it lies in C.

Unlike ordinary closure monotonicity, **I need NOT be a subset of J**:
only the selected levels strictly ABOVE the tested cut need be retained.

## Generic theorem B: full source absorption at a cut

Let X,O be any seed sets. If ∀ i∈I, c<i → i∈J, then for all z with
c≤lev(z),

z ∈ closure_J (closure_I X ∪ O)
  ⇔ z ∈ closure_J (X ∪ O).

**Proof.** Let C=closure_J(X∪O), W=C∪Low(c). The grading lemma makes W
closed over both J and I. It contains X and O. Therefore closure_I X⊆W,
so closure_J(closure_I X∪O)⊆W. A visible node z of height≥c belongs to C.
Conversely X∪O⊆closure_I X∪O; ordinary closure monotonicity gives the
reverse inclusion without a height restriction.

Notice that this does NOT assert literal equality below c. Low parameters
may occur in Yfull but not in the bare source after closure_J. The separation
is exact, not an unjustified deletion of actual Kpt nodes.

## Physical theorem C: old full source -> bare source at a real cut

Let L be an actual finite numerical-H+ model avoiding the forbidden
family, and O the set of **genuine admissible NEW Kpt original nodes**.
Let Rold be a genuine run on X at oldTop with an actual old seed at oldTop,
and Rnew a genuine run on Yfull=closure_(Rold.I0) X ∪ O at newTop≥oldTop.

At EVERY c<oldTop, let J=Rnew.I(c+1), Zfull=closure_J Yfull and
Zbare=closure_J(X∪O). Track C #218 and genuine cross-height monotonicity
give ∀q∈Rold.I0, c<q→q∈J. Therefore theorem B yields exact membership
equivalence for ALL real Kpt nodes of level≥c in Zfull,Zbare.

The following actual cut objects are consequently identical:

1. I1 source existence (a node of level exactly c).
2. I2 meet existence at c (both witnesses have level≥c because their
   meet has level c), including trivial I1-associated meets.
3. The COMPLETE choice-free \`FullPhysicalClosureCrossing\` relation of
   assigned old/upper L+ types, including E bits, negative atoms and
   all competing I2 fork outputs. Every crossing witness has lev>c.

This is the previously missing **nonvacuous, cut-local replacement** for
the all-old-levels-above-cut absorption hypothesis.

**Quantifier/scope limitation:** both closures are computed at the SAME
new-run selected set J. The theorem DOES NOT say that the genuine
AlgorithmRun on bare seeds X∪O has the SAME I-set as the run on Yfull.
It also does NOT prove that full B3 or I3 is determined by the selected
graph-age macrorecord, or that unbounded resolved copies share labels/orbits.
If a full B3 test depends only on this complete crossing and old socle, its
local verdict can be transferred by separately verified hypotheses; no
such global implication is inserted as an axiom here.

## Hostile checks

1. c=0: Low(c)=empty. No index i=0 has a parameter below 0, so the theorem
   remains meaningful, unlike the old all-above premise.
2. q=c: parameters strictly below q, hence cannot add nodes of level c.
   The exact boundary must be >=c, not >c, to preserve I1.
3. q<c: parameters and descendants stay below c; meets cannot raise them.
4. Old q>c: the theorem explicitly requires q selected at the new pre-cut
   stage; missing one invalidates the argument.
5. Original sources with different root components: meets are only made
   under SameComponent; the low-level bound holds in each component.
6. Finite parameter list may be empty: vacuous generation, still sound.
7. Duplicate Kpt original names do not affect set membership or the
   relation-valued crossing, which is allowed to fork at I2.
8. Any old seed X may have level below c; it is supplied to BOTH sources.
9. A low node already in C may meet high nodes; the result remains low.
10. A high node's parameter at q>c can be below c; it is in C by
    parameter closure over J anyway, no adverse effect.
11. New physical source O must consist of actual admissible originals,
    NOT all ancestor prefixes; the algebraic theorem would remain true
    for arbitrary O, but that would overgenerate new I1 events.
12. Numerical H+ fake source and negative E/L atoms are retained because
    equality is of actual Kpt source nodes, not of selected graph shadow.
13. K4 genuine auxiliary events 10 and 22 remain possible and are NOT
    made boring by the theorem.
14. The theorem is SOURCE LOCAL: no comparison of distinct source trees
    or changing base graph columns is claimed.
15. Even with visible closure equality, arbitrary monoid-map action,
    complete occurrence-independent source label assignment, and BRD
    remain outside the conclusion.
16. If level monotonicity of parameter nodes were relaxed to allow
    lev(x)≥i, the theorem could fail: such a parameter at i=c could
    create a new visible node. The strict S-tree grading axiom is essential.

## Validation gates

Implement finite generic lemmas and actual H+ specialization in a dedicated
Track C file and CI workflow, with strict named transitive-axiom checks and
ordinary \`lake build\` independently. Do not touch frozen black manuscript,
central Kk imports, or promote global source/orbit/BRD claims. Only AFTER
exact-head success should the olive manuscript replace the now-obsolete
"all old selected levels above each cut" application warning with the
cut-visible result; preserve a separate TODO for the as-yet-unproved
actual bare-run-vs-full-run selected-level comparison and source orbit.
