# Track C — Bare and inherited-full genuine AlgorithmRuns select the SAME levels

15 November 2026. **English FIRST, before Lean**. Stacked on graded
cut-visible source PR #233 (six named new source endpoints; exact-head
CI still outstanding at authoring). Original Track C issue #25.

## The previous open question

A true numerical-H+ new-root construction may use either the
**bare** initial seeds Ybare=X∪O (old true initial Kpt seeds plus
actual new admissible Kpt originals) or the larger source
Yfull=closure_(Rold.I0) X ∪ O, which preinserts inherited old
parameter nodes. Track E's bare physical construction proves
run existence but explicitly did NOT show it has the same
selected-level skeleton as the inherited-full run.

Track C #218 proves genuine old selected-tail retention in
a taller run. Track C #233's proposed graded closure lemma
proves the full Kpt closure **at and above any cut** is unaffected
by inherited parameter operations at levels at/below the cut,
provided the old higher selected tail is already retained.
This lets us prove much more: the TWO genuine runs select
*exactly the same numerical interesting levels*.

## Precise generic theorem

Let S be a successor tree, H an SMTree on S, and X,O sets of
tree nodes. Let Rold be a TRUE AlgorithmRun on X at oldTop=t,
with an ACTUAL seed x∈X of level t. Let T≥t, and consider TWO
true AlgorithmRuns of the SAME new scan top T:

- Rbare on Ybare=X∪O,
- Rfull on Yfull=closure_(Rold.I0)(X)∪O.

Then for every 0≤i≤T,

  Rbare.I(i)=Rfull.I(i).

No assumption of equal ordinary graph ages or a common labelled
source orbit; no restriction that old I0 omits 0 or lies above all
new tested cuts; no assumption that the two runs choose equal monoid
maps F_i (they need not).

## Proof (descending induction through true Algorithm 5.4)

Fix a candidate cut c<T. The genuine old run has
Rold.I0⊆[0,t], by its own level-set bounds. For every old selected
q>c, establish q∈Rbare.I(c+1):

- If c<t, apply Track C #218 selected-tail retention with old source
  X⊆Ybare, the true old-top seed and t≤T.
- If c≥t, no old q>c exists by Rold's selected-level bound.

Thus the old higher tail lies in J=Rbare.I(c+1). This holds
**at every cut of the new run**, including c=0 and c≥t.

At T, Rbare.I(T)=Rfull.I(T)={T} by the true runs' topI equations.
Induct downwards. Suppose Rbare.I(c+1)=Rfull.I(c+1)=J.
Use graded cutoff-visible source absorption from #233 with
I=Rold.I0 and the just-established old-tail inclusion:
for every Kpt node z of level≥c,

  z∈closure_J(Yfull) ⇔ z∈closure_J(Ybare).

The upstream genuine IsInterestingAt trichotomy at c uses:
(I1) nodes of level c, (I2) meets at c of higher nodes, and
(I3) nonexistence of one skipping MMap realizing all crossing
nodes (which have level>c). Therefore the proposed #233
IsInterestingAt cut-visible theorem makes the two **actual**
interestingness tests equivalent. In both genuine AlgorithmRuns,
an interesting cut adds c to J, while a noninteresting cut keeps
the next-stage set J unchanged. Since both runs have exactly
the same test, Rbare.I(c)=Rfull.I(c). Descending induction closes.

## Physical specialization

Take S=admissibleKptSTree family and H=normalizedKptSMTree family.
Set O to the images of genuine finiteNumericH L k M
admissible Kpt originals at the requested new root positions.
Require the real finite H+ model to avoid the forbidden family
so these originals exist, an actual top seed of Rold, true
AlgorithmRuns Rbare/Rfull, and newTop≥oldTop.
All hypotheses of the generic theorem then hold definitionally.
Hence both true runs select exactly the same levels at every cut,
even with K4 auxiliary q2 microevents 10/22.

## What this DOES and DOES NOT solve

**New, if Lean verifies:** the old concern that preinserting inherited
old closure *changes selected cuts* is eliminated under these genuine
same-height new-run hypotheses; using bare seeds is still cleaner,
but both true new-root runs have the SAME interesting-level skeleton.
Each run may use different valid skipping-map choices, and the
unfiltered closure sources can still differ below tested cuts.

**Still OPEN:** construction of the actual unbounded prescribed
resolved numerical-H+ schedule; source coordinates across genuinely
distinct base Henson occurrences; equality of full labelled inverse
source monoid orbits; relative (B3)-loss versus selected continuation
ages; optimal big Ramsey degree. The theorem does not make any
extra microevent boring or give a finite uniform BRD carrier.

## Hostile checks

1. Old I0 may contain 0: c=0 causes no problem, because q=0 is
   NOT in the selected tail q>c and parameters at q=0 cannot
   have nonnegative lower height.
2. c=t: higher old tail empty because q≤t; no false use of
   #218 outside its specified c<t range.
3. c>t: old tail again empty; equality holds at new higher
   levels by the graded parameter fact alone.
4. The index q=c is excluded from the tail because parameters
   at q are strictly lower than c; I1 at c is preserved.
5. If the old top is artificial (no real old seed at t), #218's
   top-retention proof can fail, so our theorem requires it.
6. If newTop<t the argument fails at old t; monotone height is
   explicitly required.
7. Rbare and Rfull must have the SAME newTop to compare
   descending levels; no unfiltered cross-height equality.
8. Same Kpt successor tree is essential; no unproved source
   coordinate normalization between different physical models.
9. Same numeric O is supplied to both runs. The all-ancestor
   prefix pool is NOT used as new initial seeds.
10. I3 comparison is of the genuine SMTree skip-map predicate,
    not the weaker selected-front L-only (B3) shadow.
11. The I2 alternative can have multiple upper outputs; proof
    uses full Kpt source node set, not a functional assumption.
12. No equality of Rbare.F and Rfull.F is claimed: the
    (noninteresting) skipping map is a choice.
13. A code-free/no-root component is harmless because meets
    are componentwise and graded.
14. No bound on the number of interesting cuts independent of
    newTop is established; all extra genuine auxiliary cuts stay.
15. No new Lean axiom or classical diary degree theorem is used.
16. Even exact same selected I sets do NOT give equal full
    labelled inverse-source orbits without additional transport.

## Lean acceptance gate

Formalize the generic same-selection theorem and physical
specialization *after* importing PR #233's cutoff-visible closure
and IsInterestingAt invariance. Run an isolated exact-head build,
strict two-name standard-only transitive-axiom audit, plus
independent full repository build. Do not mark a global
manuscript theorem green or merge before those gates pass.
