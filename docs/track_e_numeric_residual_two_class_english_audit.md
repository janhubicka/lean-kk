# Track E E65 — classify residual Kpt names: new final versus early old activation

**17 November 2026. English-first proof and 18 hostile checks.**
This work stacks on E64's residual new-live Kpt off-plan equivalence
(PR #276) and merged E63's actual nested numerical-H+ index construction.

## The precise two residual classes

E63 gives a SINGLE injective map \(\phi:\mathrm{Fin}P\to\mathrm{Fin}Q\)
of the actual OLD FINAL physical Kpt source names into NEW FINAL source
names. Its per-cut old-liveness implies new-liveness.

At a cut \(c\), the correct residual predicate is

\[
 \operatorname{Residual}(c,j)
 \iff \neg\exists i\in\operatorname{Fin}P:
   \operatorname{oldLive}(c,i)\wedge \phi(i)=j .
\]

A tempting shortcut would be to call every such \(j\) a "new
parameter" in the **final** closure. This is false: the same old
final node can become active in the new *pre-cut* closure earlier.
The correct case distinction is

\[
 \operatorname{Residual}(c,j)\iff
 \underbrace{j\notin\mathrm{im}(\phi)}_{\text{new final source name}}
 \quad\lor\quad
 \underbrace{\exists i\,[
      \phi(i)=j\ \land\ \neg\operatorname{oldLive}(c,i)]}
       _{\text{old-final node newly active}} .
\]

This equivalence uses INJECTIVITY of \(\phi\) in the reverse
direction. Without injectivity, two different old indices could
map to the same new index, one active and one inactive, and the
right-hand disjunction could hold even though \(j\) belongs to
the old-live image.

A \(\operatorname{newLive}(c,j)\) hypothesis is needed to regard a
residual name as an **actual present new physical node**; the
Boolean classification itself is valid for arbitrary j,
including inactive names.

## E65.1 — residual index classification

Define \`KptNewFinalName φ j\` by
\(\neg\exists i:\phi(i)=j\), and
\`KptEarlyOldName φ oldLive c j\` by
\(\exists i:\phi(i)=j\land oldLive(c,i)=false\).

For injective φ prove

\[
 \neg\operatorname{OldLiveImageAt}(\phi,c,j)
 \iff
 \operatorname{KptNewFinalName}(\phi,j)
 \lor
 \operatorname{KptEarlyOldName}(\phi,c,j).
\]

Proof by cases on membership in the image of φ.
If in image choose i. The residual condition forces
oldLive(c,i)=false. Conversely, a new-final name cannot
be old-live. If an early-old name were old-live via k,
injectivity forces k=i, contradicting its false mask.
No Kpt geometry is needed for this finite-index lemma.

## E65.2 — full physical residual criterion for TWO ACTUAL runs

The checked E63 source theorem takes ONE finite numerical-H+
Kpt structure and two actual AlgorithmRuns on literal nested
seed sets X⊆Y, with valid forbidden avoidance, real original
ambient prefix representation, oldTop≤newTop and a genuine
oldTop-level seed in X. It constructs independently exhaustive
finite final Kpt source indices and a coherent injective φ.

Apply E64's exact old-boring no-terminal theorem and its
residual-only off-plan equivalence to these constructed data.
Thus, for any prescribed allowed *source-coordinate* set,
there exist REAL source indices and a coherent φ such that

\[
 \mathrm{OffPlanNoNovelty}(R_{\rm old},R_{\rm new},Allowed)
 \iff \forall\text{ old-boring off-plan }c:
       \mathrm{ResidualQuiet}(c,\phi).
\]

The left is the complete actual finite terminal/same-node
old-and-upper dependent \(L^+\) test, not merely selected
graph-age agreement. The right now consists of tests on
new-live nodes that lie in exactly the two residual
classes above. This removes the *abstract finite source
index existence* requirement from the reverse criterion
for an actual nested numerical-H+ run pair.

**Crucial caution:** E65 does NOT prove
\(\mathrm{ResidualQuiet}\). Taking
\(Allowed=\operatorname{Bad}\) would make the conclusion
tautological and is forbidden as a claimed diary upper
bound. The intended diary construction must independently
give a uniformly finite, normalized set of genuine
auxiliary microevents and show every residual complete L+
event outside that set is already covered.

## Adversarial checklist (18)

1. Injectivity is genuinely required to identify the
   "early old" class with residuality.
2. The two classes are disjoint if φ is injective.
3. They are not disjoint in an arbitrary noninjective
   name representation; do not silently use the result there.
4. \`oldLive=false\` means a node in the OLD FINAL closure
   is not in the OLD PRE-CUT closure, not that it never existed.
5. A genuinely new final node can be inactive at the given cut;
   require newLive=true for physical novelty witnesses.
6. A newly activated old-final node can preserve node identity
   and raw full L+ records while creating a new event at a
   previously boring cut.
7. Complete full old/upper L+ crossing is a same-node
   relation, not independent old and upper spectra.
8. Full auxiliary E and false ordinary L atoms are retained.
9. I2 forks can be multivalued; do not replace the
   crossing relation by a function.
10. K4 cut-10/cut-22 q2 auxiliary events are not to be
    discarded as selected-shadow noise.
11. Actual source cuts in this theorem live in ONE physical
    finite numerical-H+ structure; not an arbitrary alignment
    between different numerical generations.
12. The true old-run top seed, nested Kpt seed sets and
    full forbidden avoidance remain assumptions.
13. The theorem constructs finite source indices in this
    setting but NOT a canonical naming of different diary
    occurrences.
14. A cut can have many residual new-live nodes and still
    be quiet because all full pairs are covered by old nodes.
15. Conversely one residual new-live terminal can force
    an I1 obstruction at an old-boring cut.
16. No numerical bound on the count of residual active names
    follows from this abstract two-class classification.
17. No successor-character assignment on selected G+ sources,
    common labelled MMap orbit, or bound of BRD is proved.
18. E64 is itself a theorem candidate pending its
    exact-head CI; E65's stack must not be merged before
    E64's direct and full checks are clean.

## Next mathematical task

Concretely analyze the two residual classes for each step of
the proposed Henson clique-block extension. Derive which
source cuts can first activate an old-final parameter and
which new final admissible nodes can carry a complete upper
\(L^+\) crossing absent from the previous source. Prove
these transitions are exactly the bounded diary
microevents (including E/q2), not arbitrary events.

This is the **actual missing geometry**. E65 gives only
the sharp finite classification and a noncircular
logical target for it. Keep the manuscript pending
and frozen black prose unchanged.

## Validation

English first, then standalone Lean: finite-index
classification, actual numerical-H+ residual-only
certificate, strict named transitive-axiom report,
and independent full build. No manuscript marks
until the actual exact-head jobs pass.
