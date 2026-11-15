# Track E E56 — used-recipe, event-indexed Kpt source reconstruction

**15 November 2026. English mathematical proof committed before Lean.**
This does not solve the diary orbit theorem. It improves the exact
conditional interface already proved in
\`Kk/FullEventIndexedOrbitBridge.lean\`; do not duplicate that
file's full-record extensionality or existing monoid-action theorem.

## Statement and local geometry

Fix two actual normalized Kpt/G+ monoid maps F,G and two full
event-indexed Kpt source records R,S with the SAME parameter-name
type and the SAME fully synchronized source-event type. Their
distinguished selected labels are Fin n. As in the existing checked
prefix-chain lemma, assume each map sends the selected source nodes
to the two target labelled copies; the two target label sequences
are **strict prefix chains** and their UNLABELLED inverse-image
source sets are equal. This last premise must be established
from physical resolved-diary geometry; equality of macro age
states or cut numbers does not imply it.

By the checked prefix-chain rigidity, R.selected = S.selected.

For each named dependent parameter p, assume both records represent
it by the **same syntactic Kpt closure recipe**
\(\rho(p)\), with three constructors:
* seed s — one of the original Kpt seeds,
* positive q — a physically selected positive parameter generator,
* meetOf u v — meet of two compatible ambient original names.

Unlike the old conditional theorem, **do not require equality of
the entire source atom assignments** atomsF = atomsG. Instead require
ONLY the following for recipe constructors ACTUALLY USED by some p:
1. If \(\rho(p)=\mathrm{seed}(s)\), atomsF.seed(s)=atomsG.seed(s).
2. If \(\rho(p)=\mathrm{positive}(q)\), corresponding positive
   parameter values are equal.
3. If \(\rho(p)=\mathrm{meetOf}(u,v)\), the two resulting ACTUAL
   Kpt meet nodes are equal. The original witnesses u,v need
   not be equal as Kpt nodes, though both underlying pair
   comparability certificates must hold.

Under the existing representation equalities
R.parameters(p)=eval(atomsF,rho(p)) and
S.parameters(p)=eval(atomsG,rho(p)), a case split on the
three constructors gives R.parameters=S.parameters. This
uses only atoms appearing in the recipes, not all unused
ambient seed/original names.

Now assume the **entire event frame** agrees at each synchronized
microevent: cut index, I1/I2/I3/B3 kind, ordered participants and
complete successor-character payload. This is NOT implied by
matching the macrodiary.

Let the selected-or-parameter source lookup namedNode be the
existing disjoint sum of the selected and dependent Kpt nodes.
We have equality R.namedNode=S.namedNode from the two previous
equalities.

Suppose physical H+ geometry supplies THREE common deterministic
reconstruction functions of exactly the event number, the full
event frame and the named source node:
\[
 \mathrm{present}(e,x),\quad
 \mathrm{oldType}(e,x),\quad
 \mathrm{upperType}(e,x).
\]
For BOTH occurrences assume their actual event-by-event presence
mask and full dependent old/upper L+ type assignments equal
the evaluations of these SAME functions. They must include E,
negative L atoms, fork alternatives and every auxiliary
microevent. Thus the masks, old types and upper types agree
by substitution of equal inputs; no separate equality
hypotheses on these three fields are needed.

By the checked FullEventIndexedSourceRecord extensionality,
**R=S as complete event-indexed source records.**

This **strictly relaxes the atom-equality component** of the old
\`full_event_source_eq_of_inverse_sets_and_recipes\` interface:
unused ambient atoms may differ. It simultaneously REPLACES the
old direct equality assumptions on presence/old/upper fields by
common deterministic reconstruction-function hypotheses. Those
are *different*, substantive premises, and the entire new
hypothesis package has **not** been proved globally weaker
than the old one. The new theorem is an alternative interface
designed for event-local geometric verification, not an
unconditional strengthening of the old orbit result.

The COMMON recovery functions, equality of full event frames,
exact selected inverse sets, physically valid meet recipes and
matched used outputs remain **open geometric obligations**.

## Adversarial checks (18)

1. The selected sources must come from genuine monoid maps.
2. The target images must be strict prefix chains in each copy.
3. Equality of unlabelled inverse-source sets is an explicit
   hypothesis; matching selected *code lengths* without a
   common source top is not enough.
4. Used seed atoms need equality only when some recipe names them.
5. Unused seed/original atoms may differ; demanding global
   atomsF=atomsG was unnecessarily strong.
6. The positive parameter case is independent of bare initial
   new-root seeding; do not preinsert all positive ancestors.
7. Meet values, not necessarily original witness names, must agree.
8. A syntactic meetOf is valid physical geometry only when both
   actual original pairs have SameComponent certificates.
9. Multiple recipes for the same node require a separate
   well-definedness/coherence proof in the H+ realization.
10. The event frame includes all auxiliary I1/I2/I3/B3 cuts,
    including the K4 cuts 10/22.
11. Ordered participant names cannot be inferred from event kind.
12. The event successor character includes fake E/negative L
    and full dependent upper assignments as required.
13. A common deterministic presence function is **assumed**
    to compute the actual full Kpt closure presence mask;
    physical source indexing alone does not provide it.
14. A common deterministic old-type function is assumed on
    *all active named sources*, not just selected front types.
15. A common deterministic upper-type function is assumed;
    equality of unlabelled permitted L-reduct spectra is false
    as a substitute.
16. Same physical bad-cut sets or terminal/crossing flags do
    not imply any of the three reconstruction rules.
17. The result is only equality of conditional event records;
    the already checked common labelled monoid transport
    additionally requires genuine target maps.
18. Neither a coherent unbounded H+ recursion nor an upper BRD
    or lower degree statement is proved by the new interface.

## Concrete next geometric obligations for Tracks B–D

- **B:** construct actual old/new original-neighbourhood columns
  and safe chronological original insertion at every event.
- **C:** provide exhaustive named dependent source closure, a
  canonical selected/positive/meet recipe for each required node,
  true meet compatibility and one source-cut normalization.
- **D:** certify correct full (B3) decisions and a deterministic
  assigned full-L+ upper-type reconstruction per participating
  source, including auxiliary E and genuine I2 forks.
- **E:** prove selected inverse-source alignment under genuine
  monoid maps and the uniform finite source-event template.
  After these premises, the existing FullEventIndexedOrbitBridge
  already provides the common labelled source and conditional
  successor-tree Ramsey transfer.

## Acceptance

An independent Lean module should import the existing orbit
bridge, prove the used-recipe and recovered-mask extensionality
without \`sorry\` or new axioms, and pass exact-head direct
compilation, strict named axiom audit, and ordinary full
\`lake build\`. No manuscript green marks or global diary
claims before the geometric application is independently proved.
