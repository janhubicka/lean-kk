# Track E E67 — one maximal eligible crossing test per actual Kpt source node

**18 November 2026. English proof and adversarial audit committed before Lean.**
This is a precise reduction of the still-open NEW→OLD full dependent-L+ crossing
coverage requirement, built on the already verified G294 lemma
\`kpt_actual_run_node_upper_covered_mono_down\`.

## Exact result

Consider TWO actual normalized-Kpt AlgorithmRuns Rold on X with top h
and Rnew on Y with top H, in ONE actual normalized Kpt source tree.
They need NOT have nested seed sets for this reduction. Fix an actual
admissible Kpt source node z and an externally specified set Allowed
of source-coordinate microcuts.

The *eligible* source cuts at which z can contribute an unwanted
old-boring crossing are the finite set

    C_z = { c < min(h,H) :
        c notin Rold.I(c), c notin Allowed,
        c < LevelTree.lev(z),
        z in closure_(Rnew.I(c+1))(Y) }.

The exclusions are ALL essential:
- c must actually be scanned by both runs (common scan range);
- c must be old-boring;
- c must be outside the allowed diary microcuts;
- z must be a genuinely NEW-LIVE source at c and must cross cut c.
  This is literal physical closure, not a selected graph-age shadow.

Let \`Covered(z,c)\` mean the actual **complete same-node**
old/upper dependent L+ crossing of z at c has one OLD physical
source witness. In the verified G294 code this is exactly
\`kpt_actual_run_node_upper_covered family X h Rold z c\`.
It is witnessed by equality of the (c+1)-ancestors of z and
a genuinely OLD-LIVE Kpt source node, which automatically
forces equality of the old type at c as well. No positive-only
projection, separated witnesses, or functional crossing choice.

### E67.1 — one-cut sufficient and necessary certificate

If C_z is empty, every required off-plan crossing test for z
is vacuous.

If C_z is nonempty, let m_z = max C_z in the **literal source
cut order**. Then:

    (∀ c∈C_z, Covered(z,c))  iff  Covered(z,m_z).

**Proof.** Necessity follows because m_z∈C_z. For sufficiency,
fix c∈C_z, so c≤m_z. At m_z the complete crossing pair of z
is realized by a single actual OLD-LIVE source node w.
The checked \`kpt_actual_run_node_upper_covered_mono_down\`
uses old-run full-source closure monotonicity and restriction
of equal genuine Kpt ancestors to transport that SAME physical
witness from m_z down to c. The maximal cut lies below oldTop
by its membership in C_z, so the checked theorem applies.

Consequently,

    (∃ c∈C_z, ¬Covered(z,c))  iff  ¬Covered(z,m_z).

This gives a **frontier witness**: if this fixed source node
has any unplanned uncovered complete crossing, then its
*HIGHEST ELIGIBLE* crossing cut is also uncovered.

Thus one needs at most ONE complete pair-cover test per actual
new-source Kpt node, instead of testing this node at every
old-boring off-plan cut. There is no bound on the number of
different nodes to test, nor on how many cuts one node could
contribute to the bad set if its maximal test fails.

### Relationship to G294/G298 and E64/E65

G294's per-node novel crossing support is an interval, and
G298 shows every physical bad cut is covered by terminal
or one-node interval witnesses in the common scan range.
E67 takes a different, application-facing consequence:
ONE maximal *eligible* cut is a complete test for whether
one particular node creates ANY unplanned crossing failure.

The eligible set may have gaps because old interesting
levels and the Allowed diary microcuts are removed;
E67 does not assert C_z itself is an interval.
The downward persistence of OLD coverage makes the
maximal-cut criterion valid even when C_z is disconnected.

E64/E65 restrict attention to residual NEW-LIVE names,
which include NEW FINAL nodes and OLD FINAL nodes
activated earlier. E67 can be applied to all of these;
matched OLD-LIVE names are already covered by the
verified coherent physical node-identity map.
As a future corollary, one may apply E67 only to residual
indices in the actual E63 finite source, after checking
their true per-cut activity and the physical old-node map.

**Do not reverse the direction of the implication:**
missing coverage at one LOWER cut does NOT force missing
coverage at every lower cut. It forces failure at the
MAXIMAL eligible cut, by contraposition of the covered
downward-monotonicity theorem.

## Adversarial checklist (20)

1. Both runs must be GENUINE normalized Kpt AlgorithmRuns.
2. The cuts lie in ONE common Kpt source coordinate system.
3. Use \`min oldTop newTop\`; the newer run can be shorter.
4. Old-boringness is checked against the actual \`Rold.I(c)\`.
5. Exclude each explicitly ALLOWED auxiliary E/q2 microcut.
6. The K4 q2 cuts 10 and 22 must not be silently dropped.
7. z is an actual admissible Kpt node and must be NEW-LIVE.
8. Require c<lev(z); equal-level terminals are an I1 case,
   not a complete crossing with an upper (c+1)-ancestor.
9. The OLD witness is one actual pre-cut Kpt node.
10. One matched upper ancestor supplies BOTH old and upper
    complete L+ types, including E and negative ordinary L.
11. Forks at I2 may give multiple nodes, all separately tested.
12. The eligible set can be empty; never take an unsupported max.
13. max C_z is a source cut, not a numerical H+ target gap.
14. The eligible set need not be order-convex after removing
    allowed or interesting cuts.
15. Old crossing coverage persists DOWNWARD; missing coverage
    propagates UPWARD in its contrapositive form.
16. One maximal test can fail while the node is covered at many
    lower cuts; it does not bound interval length or bad cuts.
17. A cut-level TERMINAL has no upper crossing and must be
    checked separately (at most its literal level per node).
18. A finite source index from E61/E63 gives finitely many
    nodes, not a UNIFORM diary-dependent source carrier.
19. Different diary occurrences may have different physical
    source tops/indices and their cut reindexing is still open.
20. No common labelled inverse-source MMap orbit, corrected
    B3 relative-continuation theorem or sharp BRD follows.

## Remaining geometric acceptance

To use this for the desired upper bound, construct one
uniformly controlled resolved-diary finite source template;
match its genuine Kpt physical nodes and assigned successor
characters across occurrences; and prove OLD coverage at
the maximal eligible cut of EVERY residual new-live node.
Also certify the separate I1 terminal level for each such
node. Without controlling how many nodes/types the diary
actually generates, reducing to one test per node does NOT
yet prove precompactness or a BRD upper bound.

## Lean gate

New independent module importing the verified G294
TrackGCrossingFrontier and E65 residual-source definitions.
Prove exact eligible-cut membership, max-cut iff,
and missing-pair frontier iff, no \`sorry\`/nonstandard
axioms. Run source-exact direct build, strict named
\`#print axioms\` parser, independent full build.
No manuscript validation marks until these pass.
Frozen black mathematics and removed TODOs untouched.
