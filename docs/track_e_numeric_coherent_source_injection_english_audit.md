# Track E E63 — a real finite numerical-H+ run pair has a coherent all-cut Kpt source-name injection

**16 November 2026. English mathematical proof and adversarial tests written BEFORE Lean.**
Stacked on conditional E62 PR #267, which itself imports E60.

## What is actually discharged

E62 still assumes the existence of independently exhaustive
finite old/new final Kpt node indices, with exact live masks
at all old scanned cuts. These are not arbitrary new
assumptions in the finite numerical-H+ setting: the checked
\`finiteNumericH_actualRun_uniform_exhaustive_source_index\`
constructs each index for a GENUINE finite numerical-H+ Kpt
AlgorithmRun when the real forbidden-family avoidance and
physical ambient-prefix-source premises hold.

E63 specializes E62 to exactly these constructed indices.

## Precise result

Fix one finite numerical-H+ structure \`finiteNumericH K k N\`
whose FULL ordinary-L reduct avoids the normalized forbidden
family. Choose physical Kpt seed sets \`X⊆Y\`, BOTH lying
in the genuine source \`ambientPrefixPool family
(finiteNumericH K k N) hAvoid U\`.
Let \`RunOld\` be a real normalized Kpt AlgorithmRun on
X of height h and \`RunNew\` a genuine run on Y of
height H≥h, with a real old seed at level h.

Then one can construct:

1. Finite actual source sets \`oldParams,newParams\`
   consisting EXACTLY of the respective true final
   Kpt meet-and-parameter closures.
2. Their canonical finite enumerations
   \`oldNode : Fin oldParams.card→AdmissibleKptNode\`
   and \`newNode : Fin newParams.card→AdmissibleKptNode\`,
   both injective and physically sourced.
3. Exact per-cut Boolean source activity masks
   \`oldPresent, newPresent\` satisfying at every c<h
   an IFF with membership in the respective COMPLETE
   physical pre-cut closure \`closure_(Run.I(c+1))\`.
4. One single injective \`φ : Fin oldParams.card →
   Fin newParams.card\`, chosen BEFORE all cuts,
   such that \`newNode(φ i)=oldNode i\` for all
   old parameter names i.
5. For every source cut c<h,
   \`oldPresent(c,i)=true ⇒
   newPresent(c,φ i)=true\`, and BOTH literal
   complete same-node raw old/upper dependent L+
   ancestor \`Option\` records are unchanged.

The proof is short but depends on real geometry:
run the independently verified finite numerical-H+
exhaustive index construction twice, form the full
final new-index membership equivalence from the
\`Finset.equivFin\` bijection, use old-name membership
in the real final old closure, and invoke E62's
coherent physical source transport. The per-cut
exactness equivalences come directly from the two
actual exhaustive index constructions. There is no
new ad hoc finite naming assumption.

The result is for two **nested seed sets of the SAME
physical finite numerical-H+ structure**. It is not
a common source map between two unrelated numerical
generations or different resolved-diary occurrences.

## Adversarial audit (20 cases)

1. Both run inputs must be true Kpt AlgorithmRuns;
   an arbitrary hand-picked selected-level sequence is
   not enough.
2. Require the forbidden-family avoidance of the FULL
   actual finite numerical-H+ ordinary-L reduct.
3. Both X and Y must lie in the actual normalized
   ambient prefix pool; selected graph-age shadows
   do not give this.
4. Require **literal X⊆Y** in the SAME Kpt source tree.
5. Require h≤H and a true old seed of level h.
6. The final source index is closure at \`I 0\`,
   not the earlier pre-cut source or the selected
   original-name pool.
7. Do not require oldParams.card=newParams.card.
8. Both index maps are actual bijective enumerations
   of their respective finite source-node Finsets.
9. The constructed map φ is injective but not
   asserted surjective: new sources may have many
   extra dependent Kpt nodes.
10. Final old closure is contained in final new
    closure by actual run height/seed monotonicity;
    no false equality is used.
11. Per-cut membership is a Boolean IFF, not a
    selected-level or age-state approximation.
12. The SAME φ preserves old per-cut liveness at
    every c<h, not a new choice j(c,i).
13. The complete raw old/upper L+ Option values
    are evaluated on exactly identical admissible
    Kpt nodes; all E/negative binary/unary/diagonal
    atoms survive.
14. The old->new physical crossing relation may be
    a strict subset of the new one; I2 forks can
    increase without invalidating the theorem.
15. Reverse new->old source matching/off-plan
    no-novelty remains completely open.
16. OldTop=0 is allowed by the formal theorem;
    any actual old seed then has level zero, and
    scanned-cut claims are vacuous. This does NOT
    produce an interesting positive-height diary
    bound by itself.
17. NewRoot may add a single real original-only
    seed as a specialization, but the theorem does
    NOT preseed all its ancestor nodes.
18. All scan indices are *actual source* cuts;
    different ambient numerical generations have
    not been canonically reindexed.
19. Selected G+ source vertices and event successor
    characters are NOT automatically carried by
    this dependent Kpt parameter injection.
20. The result gives no uniform diary event carrier,
    common labelled inverse-source monoid orbit,
    upper BRD theorem or independent lower bound.

## Remaining mathematical acceptance gate

Construct such *nested* physical stages throughout
the proposed resolved infinite Henson subcopy, normalize
source coordinates and bound/identify the genuinely
new dependent Kpt nodes and their complete L+ upper
assignments by a diary-derived finite microevent list.
E63 handles old-parameter retention in one finite
physical extension only. It cannot identify the new
nodes with those of a different diary occurrence.

## Validation

Import E62 and the actual exhaustive numerical-H+
run-index module in a NEW independent Lean file.
Prove one fully elaborated existential theorem,
compile at its exact PR head, run the dedicated
strict named standard-only transitive-axiom audit
and ordinary full repository build.
No green or blue manuscript mark before both pass.
No frozen black mathematics altered.
