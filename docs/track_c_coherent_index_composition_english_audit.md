# Track C — composition of physical coherent Kpt source indexes

17 November 2026. **English-first proof / adversarial audit before Lean.**
Starts from exact-head certified Lean main \`5ee2ee59e3d2b7367cee77d27e9babc7d2680a4f\`, which centrally registers 867 named standard-only axiom checks and imports \`Kk.ConstructedPhysicalOldNewSourceIndex\`. That original theorem came from Track C PR #288, and has its separate full and axiom build. This note does not require its concrete huge signature.

## Actual existing invariant and the gap

Track C #288 constructs an injective \`φ : Fin P → Fin Q\` between complete old/new physical Kpt source-index universes. It has literal node identity
\`newNode (φ i)=oldNode i\`, and preserves each old-live source mask at all cuts strictly below the old scan top, including all full assigned old/upper \`L^+/E\` types. Its direction is **old→new**, not reverse.

For a sequence of NEW roots, one must compose these maps. Existing one-step source results alone are not yet a *single coherent cumulative indexing invariant* unless composition is formalized and all cut horizons respected. A mistaken unqualified equality of old/new cardinalities or reverse new→old match would eliminate genuinely new q2 auxiliary source nodes, so it is UNSOUND.

## Precise abstract source-index object

Fix the SAME Kpt forbidden-family type and three finite injective
index universes \`A,B,C\` (the actual index maps can be concrete \`Fin P\`,
\`Fin Q\`, \`Fin R\`). Each universe is labelled by actual admissible
Kpt nodes in the SAME normalized successor tree. A coherent map of
horizon t is a function \`φ:A→B\` with:

1. \`φ\` injective;
2. \`B.node(φ(i))=A.node(i)\` **literally** for every i;
3. for every cut c<t, any old source live at c is new-source live
   at c on \`φ(i)\`.

Complete type preservation
\`kptFullOldAtCut(B.node(φ i),c)=kptFullOldAtCut(A.node i,c)\`
and the same for upper types follows directly from (2). There is
no independent E or L atom oracle: it is the exact Kpt node.

### Composition theorem

For \`φ:A→B\` coherent through t, and \`ψ:B→C\` coherent through u,
\`ψ∘φ:A→C\` is coherent through \`min(t,u)\`.

**Proof.** Composite injectivity follows from each factor.
For every old i,
\`C.node(ψ(φ(i)))=B.node(φ(i))=A.node(i)\`.
For c<min(t,u), first use φ's live implication at c,
then ψ's. Every old record and its ordinary/auxiliary
\`L^+/E\` atoms is literally the same Kpt source node at the end.
The intermediate indexed source is the *same* B on the two edges;
this is essential to typecheck the composition.

The identity map is coherent at every horizon (no finite cutoff
needed). Composition of underlying maps is associative by ordinary
function composition; the cutoff \`min\` is associative.

## Adversarial checks

1. **Different horizons:** c belongs to the composite domain only
   when c<t AND c<u; using max(t,u) would be false.
2. **Old-to-new only:** no new-to-old surjectivity; q2-type source
   nodes may be newly live and have no old antecedent.
3. **Injectivity:** composite injectivity is essential to avoid
   collapsing multiple named old source nodes.
4. **Duplicates:** the concrete actual finite source theorem uses
   injective enumerations; different nodes cannot be assigned the
   same physical index after transport.
5. **Same Kpt tree:** source-node equality is not a map between
   two unrelated occurrence encodings. External source coordinate
   normalization remains open.
6. **I2 forks:** several complete upper types sharing one old
   source are retained because source nodes themselves are
   transported, not merged by their L reduct.
7. **Negative atoms/fake E:** all preserved literally by node
   equality, not just ordinary positive edges.
8. **c=0:** works even if the source has actual level-zero I1.
9. **Empty P:** coherence is vacuous; no unproved nonempty source
   assumption is needed.
10. **New nodes:** any new node in B or C outside the old image
    remains unconstrained, permitting genuine auxiliary events.
11. **Genuine range:** theorem does not manufacture an old→new
    stage map; Track C #288 supplies each one under its separate
    physical H+ hypotheses.
12. **Finite iteration:** any finite chain of actual one-step
    maps can be composed, but one still needs a physically
    realized UNBOUNDED recursive schedule and a uniform
    diary-indexed source orbit to prove the BRD theorem.
13. **Monoid-map confusion:** this is an injection of finite
    source indices, NOT an \`MMap\` of the successor tree, and
    does not automatically preserve chosen skipping maps F_i.
14. **No global cardinal bound:** finite P,Q,R depend on actual
    finite physical numerical H+ stages.
15. **No equality of selected diary profiles:** the theorem
    is independent of graph-age macrorecords and cannot
    project I3 or B3 from selected shadow values.

## Acceptance

Implement one small Lean file in its own branch, with an exact-head
standalone module build and strict named standard-only axiom checks.
Do not change frozen black manuscript prose or promote any global
BRD or labelled-orbit mark. The intended next Track C integration is
a short olive paragraph identifying this *finite compositional*
source transport and the still-open distinct-occurrence orbit gap.
