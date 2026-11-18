# Track G — E54 canonical off-plan bad set controls synchronized whole-run transport

18 November 2026. English proof and adversarial audit FIRST.

## Purpose

Make the independently verified Track E finite certificate directly
usable for the new Track G boring-only no-novelty theorem (PR #365).
The result is stronger than an old-range sandwich because no input
Y-run is needed: it constructs an actual run on Y with unchanged
selected I and total monoid-valued F.

Fix one normalized Kpt family, nested actual source seeds X⊆Y,
one old genuine AlgorithmRun RX on X with scan top t, and exact
finite full Kpt node indices `oldNode/liveOld`,`newNode/liveNew`
at EVERY old cut i<t for

  ZX(i)=closure(S,RX.I(i+1),X),
  ZY(i)=closure(S,RX.I(i+1),Y).

These indices refer to RX's selected I tails on BOTH source sides.
They are not selected-front ordinary-L age indices, and no
AlgorithmRun on Y is assumed.

## Theorem A: E53's actual no-offplan certificate is sufficient

Assume

  KptTwoIndexOffPlanNoNovelty(family, RX.I, t, Allowed=∅,
                              oldNode,newNode,liveOld,liveNew).

The Track E E54 theorem `kptTwoIndexOffPlanNoNovelty_iff_quiet`
shows that for every cut i<t with i∉RX.I(i), the *complete*
`KptIndexedQuietAtCut` holds. For any actually BORING old cut i,
the genuine `RX.noninteresting_step` gives

  RX.I(i)=RX.I(i+1).

By the true AlgorithmRun selected-level bound, every level
in RX.I(i+1) is ≥i+1; consequently i∉RX.I(i).
Therefore E54 quietness holds at EVERY OLD-BORING cut.

The already verified G365 indexed boring-only theorem transforms
these exact finite quietness certificates into one genuine
AlgorithmRun RY on Y with

  RY.I = RX.I,    RY.F = RX.F.

No equality or bijection of source-index domains, no E1, and
no Y-run are assumed. The established source inclusion X⊆Y
guarantees interesting cuts of RX remain interesting; quietness
is demanded only at old boring cuts.

## Theorem B: zero intrinsic canonical Bad cuts is enough

Let `kptCanonicalOffPlanBadCuts` be E54's MINIMAL Finset of
old-boring source-coordinate cuts failing the full finite indexed
terminal-plus-paired-L+/E no-novelty test. Suppose

  kptCanonicalOffPlanBadCuts(family,RX.I,t,oldNode,newNode,
                             liveOld,liveNew) = ∅.

By the verified exact equivalence
`kptTwoIndexOffPlanNoNovelty_iff_badCuts_subset`, this means
the finite off-plan certificate holds with Allowed=∅.
Apply Theorem A. Hence zero canonical Bad cuts suffices to
construct the same-I same-F target run on Y.

The theorem is NOT an equivalence: extra new crossings can
possibly be respected by the same skipping map even when
physical profile equality fails. Bad is a sufficient
quietness obstruction, not necessarily the exact obstruction
to existence of some synchronized run.

## Adversarial audit

1. The exact old/new finite source indices are on the ORIGINAL
   RX.I tails; this does not assume or infer a Y-selected scan.
2. Both indices must include all generated dependent parameters,
   meets, terminal nodes and full paired L+/E atoms.
3. E53's `oldSelected` argument must be RX.I, not an
   ordinary macrodiary selected-front level mask.
4. The mask Allowed must be literally empty for no exceptions;
   allowing exceptional cuts does NOT give a whole same-I/F run.
5. The E54 predicate checks ONLY old-boring cuts; this is
   exactly what the G365 stronger transport theorem needs.
6. The actual old-boring implication i∉RX.I(i) comes from
   `noninteresting_step` and `I_mem_bounds`, not an assumption
   about the abstract selected-front graph ages.
7. Even if a cut has no actual old terminal, I2 and I3 still
   require full same-node paired L+/E crossing quietness.
8. No I2-free or raw type-functionality assumption is made.
9. Genuine K4 auxiliary microcuts 10 and 22 can cause a
   nonempty canonical Bad set and thus block this theorem;
   no such events are discarded.
10. The entire total monoid function F is preserved only for
    the synchronized target run constructed; other Y-runs
    need not share its total F.
11. A zero finite Bad set does not imply equal inverse-image
    sources of distinct X,Y under that common map F.
12. Full source-index sizes may differ and no index bijection
    or reverse transport is supplied.
13. No chronological cut-coordinate transport between
    differently enumerated diary occurrences is constructed.
14. Empty canonical Bad in one concrete finite source does
    not give a uniform event budget for every physical growth.
15. The unbounded numerical-H+ resolved copy, complete (B3)
    versus relative continuation and common labelled
    inverse-source orbit remain outstanding.
16. No lower-colouring or exact Kk-free BRD theorem is proved.

## Lean acceptance

Import G365, E54 canonical bad-cuts and genuine AlgorithmRun
source bounds. Formalize (1) direct E53 finite off-plan
certificate ⇒ same-I/F Y-run and (2) empty canonical Bad
Finset ⇒ same-I/F Y-run. Dedicated two-name standard-only
direct CI and independent full Lean build; no global
manuscript green promotion.
