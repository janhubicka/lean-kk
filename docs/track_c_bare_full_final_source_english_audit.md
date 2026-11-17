# Track C: bare/full actual new-root source identity after selected-level synchronization
16 November 2026. English proof BEFORE Lean, adversarial boundary audit.

**Stack:** audited cut-visible six-theorem PR #233 merged to main, then
staged bare/full run selected-level equivalence PR #240; this note is
a NEW, separate child workstream and must not be merged ahead of #240.
No appeal to a published K_k BRD formula or abstract diary axiom.

## Inputs and theorem statements

Let H be any genuine SMTree on a successor tree S, and let X, O be
two sets of nodes. Let the old genuine AlgorithmRun Rold on X have
height t, and assume that X contains a node of level t (a REAL old
top seed). Fix new height T≥t and two genuine new AlgorithmRuns at
the SAME T:

  Rbare : AlgorithmRun H (X ∪ O) T,
  Rfull : AlgorithmRun H (closure_S(Rold.I0, X) ∪ O) T.

By the proposed theorem in PR #240, Rbare.I i = Rfull.I i at every
i≤T. The present corollaries prove two additional things.

### A. Final parameter-closed sources are literally identical

  closure_S(Rbare.I0, X∪O)
    = closure_S(Rfull.I0, closure_S(Rold.I0, X) ∪ O).

**Proof.** Since X⊆X∪O, the already kernel-checked cross-height
seed-selection monotonicity (#196 / #218) implies
Rold.I0⊆Rbare.I0; this holds even if 0∈Rold.I0. The already
kernel-checked generic absorption identity (PR #192),

  closure_J(closure_I X ∪ O) = closure_J(X∪O)    if I⊆J,

applied to I=Rold.I0, J=Rbare.I0, gives literal equality on ALL
Kpt nodes. Finally PR #240 gives Rbare.I0=Rfull.I0.
No cutoff/truncation is needed at the FINAL selected set.

Thus, in the actual numerical H+ Kpt specialization, the
terminal complete finite source, old/upper assigned L+/E
partial-type data and dependent parameter nodes are the SAME
for both seed presentations, even if one source initially
preinserted closure nodes.

### B. At every earlier tested cut, visible source records agree

For c<T put J=Rbare.I(c+1)=Rfull.I(c+1).
All old selected q>c lie in J:

* when c<t: use the genuine old-tail retention theorem of #218;
* when c≥t: the old run bound q≤t makes this vacuous.

Hence PR #233's graded cutoff absorption yields

  z ∈ closure_J(X∪O)
     iff z ∈ closure_J(closure_(Rold.I0) X∪O)
  for all actual nodes z of level at least c.

For a numerical-H+ model whose actual original nodes avoid the
forbidden family, this implies exact equivalence of:
- I1 source at c;
- I2 meet at c, including I1-trivial meets and competing forks;
- the COMPLETE choice-free old/upper dependent L+ crossing relation
  at c, including every negative ordinary L-atom and auxiliary E;
- actual I3 \`IsInterestingAt\` based on nonexistence of a skip
  monoid map for ALL crossing nodes.

Every statement is a property of two runs of the SAME underlying
physical normalized Kpt structure and the same set O of genuine
new original Kpt nodes. The theorem does not compare different
ambient base models or identify source coordinates across embeddings.

## Extra hostile checks

1. t=0,T=0: both final selected sets are {0}; the closure
   identity still holds. There are no tested cuts c<T.
2. Old I0 includes 0: source equality still holds, since Iold⊆J
   at final, and the cut-local argument discards only q≤c.
3. The two new runs may use different MMap values F_i; this
   proof compares actual sets I_i and source closures, not F_i.
4. Two distinct old originals can produce the same Kpt node:
   set equality and relation-valued crossing preserve both outputs.
5. Each genuine source node carries its own E and L+ atom
   records; these are not independently reconstructed from
   selected graph-age shadows.
6. Real K4 auxiliary cuts 10,22 are preserved whenever selected;
   the corollary never declares them boring.
7. Without actual old top seed, old I0 need not persist and the
   equal-final-source conclusion can fail; retain the hypothesis.
8. If newTop<oldTop, the old selected tail need not be present.
9. The old source X may itself contain legitimate dependent
   Kpt nodes, but O contains only genuine NEW original nodes.
10. The all-ancestors new-root pool is still forbidden as a
    substitute for O: it can force I1 saturation independently
    of the present final-closure equivalence.
11. A separately chosen bare-run source and inherited-full-run
    source have equal *final* closure only after equal selected
    I0 has been proved by PR #240; do not erase that prerequisite.
12. Actual full source equality does not furnish a uniform
    finite carrier size independent of the numerical height.
13. It does not establish an occurrence-independent labelled
    inverse source orbit: two DIFFERENT occurrences need further
    source-coordinate and dependent-label transport.
14. The additional equivalence of I3 at c uses the true
    \`IsInterestingAt\` map nonexistence, not the paper's
    graph-age-only (B3) approximation.
15. No conditional relative age-loss ↔ physical B3-loss
    bridge is discharged by this theorem.
16. Do not promote global K_k-free big Ramsey degree claims;
    these are local source-canonicalization results.

## Acceptance

Keep this as a separate draft/stacked PR, with exact direct-module
build and standard-only \`#print axioms\` audit. Then full \`lake build\`
at the dependency-integrated head; only after those pass should the
olive manuscript promote these LOCAL new-root conclusions to
source-pinned BLUE (not globally GREEN) validation marks.
Frozen black text and existing source pins are not changed.
