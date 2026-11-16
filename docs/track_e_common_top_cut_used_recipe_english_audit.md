# Track E E58 — replace inverse-image-set equality by a common source top and selected source cuts

**16 November 2026. English-first proof, adversarial audit before Lean.**

This is a **different conditional route** to equality of full
event-indexed Kpt/G+ source records. It composes existing verified
\`Kk.PrefixCutRigidity\` and merged E56 used-recipe recovery.
It does not repeat either underlying theorem, and does not
derive a common source top from the proposed diary.

## Geometric motivation

E56's checked \`full_event_source_eq_of_used_recipes_and_recovery\`
requires equality of the complete UNLABELLED inverse-image
sets of all selected targets under two genuine Kpt monoid maps.
This is a strong, global preimage comparison. It might be easier
to certify source labels from **one genuine common top code and
one chosen source length per label**.

\`Kk.labelled_sources_eq_of_common_top_and_cuts\` already proves
that such a top-and-cut dictionary determines a labelled
prefix chain, provided both target chains really are images
of that top under their genuine source shape maps. This is
the right theorem to reuse, not a new combinatorial claim.

## Exact E58 English statement

Let F,G be actual normalized-Kpt monoid maps and R,S be
full **event-indexed** records with selected labels \`Fin n\`
and the SAME parameter-name/event/frame types.

Assume one common actual finite G+ source top \`sourceTop\`
and two genuine target tops \`targetTopF,targetTopG\` with

\[
 \widehat F(sourceTop)=targetTopF,\quad
 \widehat G(sourceTop)=targetTopG.
\]

Assume each labelled target \`targetF(a)\`/\`targetG(a)\`
is exactly the image of \`R.selected(a)\`/\`S.selected(a)\`,
and is a G+ code-prefix of its corresponding target top.
Finally, for every selected label a, assume the SOURCE
code lengths agree:

\[
  |R.selected(a)|=|S.selected(a)|.
\]

The checked prefix-reflection theorem turns each target-prefix
condition into a source-prefix condition under the SAME
\`sourceTop\`. Uniqueness of a finite code prefix at a specified
length gives, **label by label**,

\[
  R.selected(a)=S.selected(a).
\]

This conclusion needs NO equality of whole selected inverse-image
sets, no enumeration of an unlabelled source range and no
abstract source-node bijection.

Now assume the same literal Kpt closure-recipe schema for named
dependent parameters in both records. Following E56, require
only equality of ACTUALLY USED seed/positive/compatible-meet
outcomes. Then \`R.parameters=S.parameters\`.

Lastly require the entire synchronized event frame
(source cut, event kind, ordered input list and successor
character) to coincide, and require the two records' actual
per-event **presence, complete old L+ and assigned upper L+**
fields to be recovered by the **SAME** functions of the full
event frame and named G+/Kpt source node. The resulting
source-node lookup functions agree, so those three fields
agree at every event. Full event-indexed record extensionality
proves **R=S**.

This is a **replacement of selected-source hypotheses**, not
an unconditional weakening of all E56 hypotheses: it introduces
a common source top and matched selected source lengths, while
retaining E56's separate and substantive full-event recovery
assumptions. Neither set of geometric hypotheses is supplied
by the bare macrodiary yet.

## Adversarial checklist (18)

1. The monoid maps F,G are actual Kpt MMaps, not arbitrary
   functions on finite graph-age states.
2. The same \`sourceTop\` is a genuine finite G+ code in the
   common normalized Kpt source tree.
3. Both \`targetTopF\` and \`targetTopG\` must be actual images
   of \`sourceTop\`; equal LENGTHS of target tops are not enough.
4. Every selected target is a genuine code-prefix of its
   corresponding target top, including all finite L+ E bits.
5. Target selected labels must be their ACTUAL image values.
6. Selected source lengths are compared in SOURCE coordinates;
   numerical H+ target index gaps can differ.
7. Equality of source lengths WITHOUT a common source top
   does not identify source G+ codes.
8. Equality of a common source top and lengths identifies
   source G+ ordinary-socle codes, but does NOT automatically
   identify distinguished Kpt type-vertex data hidden by
   the \`RawPartialTypeNode.ordinaryCode\` forgetful map.
9. Raw Kpt parameter nodes are a distinct sort from
   selected finite G+ source codes; do not conflate them.
10. Used meet recipes require genuine SameComponent input
    certificates on both occurrences.
11. Names/recipes for all dependent Kpt parameters must
    be complete if the theorem is applied to an entire
    AlgorithmRun pre-cut closure. The equality proof
    itself does not assert \`CoversParameterClosure\`.
12. A common E/S/A/C macro event kind does not determine
    ordered participating sources, source cut or upper L+
    successor character; the full frame is a premise.
13. The same deterministic presence function is still
    assumed to describe actual source activity.
14. The same deterministic full old/upper L+ recovery
    functions are still assumed, not derived from B3
    verdicts or selected graph-age values.
15. The raw L+ record retains positive/negative directed
    binary, unary, diagonal and auxiliary E atoms, and
    all I2 alternatives on their actual named source nodes.
16. The K4 q2 physical cut-10/22 auxiliary regression must
    remain in any genuine event-indexed diary template.
17. The existing local-Kpt trace-blindness counterexample
    shows that equal cut verdicts alone cannot replace
    source-node reconstruction and participant incidence.
18. Equality of full event records alone does not manufacture
    genuine MMap target transport nor a uniform finite
    labelled carrier/BRD upper bound.

## Connection to E57 and remaining genuine geometry

E57's [PR #249](https://github.com/janhubicka/lean-kk/pull/249)
will, if its exact-head Lean checks pass, replace generic
recovery functions for **named physical Kpt parameters** by
actual source activity and literal \`kptFullOldAtCut\` /
\`kptFullUpperAtCut\` raw ancestor calculations.
E58 is independent of E57; it still uses the generic
event-recovery functions. Once both are certified, a further
composed interface could combine common-top-and-cuts selected
source equality with physical parameter trace reconstruction.

**Still open:** A genuine recursively resolved numerical-H+ diary
must supply one normalized source top, the correct source cut
number for each selected label, actual full source recipes,
activity in both source closures, exact event/microevent frame
identity and compatible monoid maps, uniformly over its
occurrences. This is the actual geometric orbit theorem.

## Verification and manuscript discipline

Commit this English proof and hostile checklist BEFORE Lean,
then prove the conditional result in an independent module.
Require an exact-head module build, the standalone strict
transitive-axiom audit and a separate full repository build
before marking any new statement validated. Do not change
frozen black mathematics or promote the global orbit/degree.
