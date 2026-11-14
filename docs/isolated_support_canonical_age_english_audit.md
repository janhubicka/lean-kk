# Track A — actual reserved raw age and ideal cover have identical canonical ages

**14 November 2026. English proof and adversarial audit before Lean.**

This module is the exact missing link between merged `Kk/IsolatedSupportBlockRawAge`
(PR #179) and `Kk/FiniteSupportCoverProfile` / `Kk/IntegerWitnessCanonical`.
It does NOT identify the two RAW bound functions pointwise. It proves
something stronger and correct about their **whole normalized integer
witness sets and their canonicalizations**, without needing a chosen
finite future graph.

## Fixed mathematical input

Let E be an arbitrary directed Boolean original graph, ell,d natural,
P,Q disjoint finite original pools, and suppose E(p,q)=0 for every
p in P and q in Q. Fix complete old-to-future typed columns c and
one admissible nonempty support T. Let
  rho(U) = cliqueCap_E({p in P: every t in U has c(p,t)=1}),
  a = cliqueCap_E(Q),
  B(U) = ell-1-rho(U).

After inserting the isolated reserved block Q, its entire future
typed column is 1[t in T], zero outside T. The verified literal
raw bound (PR #179) is
  Bnew(U) = ell-1-(if U subset T then max(rho(U),a) else rho(U)).
The ideal one-coordinate raw cover bound is
  I(U) = if U=T then min(B(U),ell-1-a) else B(U).

**Do not claim Bnew=I.** If U is a PROPER subset of T, Bnew(U)
may decrease even though I(U)=B(U).

## Lemma A: exact complete feasible-weight characterization

A normalized integer clique weight w respects every Bnew(U) iff
  (i) w respects B(U) at EVERY nonempty support U, and
  (ii) w(T) <= ell-1-a.

Forward: the independently checked raw monotonicity Bnew<=B gives (i).
At U=T, the literal raw formula says
  w(T) <= ell-1-max(rho(T),a) <= ell-1-a,
giving (ii). No subtraction-cancellation is assumed.

Reverse: assume (i) and (ii). If U is not contained in T,
Bnew(U)=B(U), so (i) suffices. If U subset T, nonnegativity of
individual multiplicities gives w(U)<=w(T)<=ell-1-a. Together
with w(U)<=ell-1-rho(U), it gives
  w(U)<=min(ell-1-rho(U),ell-1-a)
       =ell-1-max(rho(U),a)=Bnew(U).
The identity involving truncated Nat subtraction is valid for every
ell,a,rho, even when a>=ell or Bnew=0. No hidden positivity hypothesis.

This proof quantifies over EVERY support U and EVERY normalized
weight vector w. It does not require W to be a clique or a
particular geometric realization.

## Lemma B: ideal one-coordinate cover has EXACTLY the same conditions

By its definition, w respects all I(U) iff it respects all B(U)
and w(T)<=ell-1-a. This is true even when a>=ell, when the
threshold becomes zero. Therefore

  for all normalized w:
    WitnessRespects(Bnew,w) iff WitnessRespects(I,w).

In particular the finite sets of all raw-feasible normalized
integer weight vectors are *identical*, not merely equal in their
maxima or their values at T.

## Canonicalization equality — the key missing bridge

The integer graph-age canonicalizer is the pointwise supremum over
exactly the normalized witness vectors respecting the raw bound.
Since the witness sets coincide,

  integerGraphAgeCanonical(d,ell,Bnew)
    = integerGraphAgeCanonical(d,ell,I)

POINTWISE AT ALL NONEMPTY SUPPORTS.

This is an equality of canonicalized graph-age functions, not
of the physical RAW common-neighbour bounds. It is valid even
if Bnew or I are not positive/genuine graph ages.

A further general identity is useful:

  G_(rawCliqueBlockBound ell a B T)
    = G_(rawCliqueBlockBound ell a G_B T).

It follows since canonicalization itself preserves exactly
the normalized feasible witness vectors of B, and imposing the
same additional threshold at T preserves equivalence.
It avoids assuming B=G_B pointwise.

## Actual canonical cover consequence

Suppose the pre-block canonical age satisfies G_B=upper,
and lower ⋖ upper is a genuine one-step integer graph-age cover with
  ell=lower(T)+r+1,
  upper(T)=lower(T)+1,
  a<=r.
Then the already checked canonical cover-block theorem gives

  G_Bnew = if a<r then upper else lower.

No claim of real physical stage existence is made here; Q is an
arbitrary ACTUAL finite pool with the stated isolation/columns
and clique capacity a. In a Henson stage Q will be constructed by
the separate checked left-density reserved-clique theorem.
For a literal reserved **clique**, a=|Q|, but no cardinal shortcut
is used in the general theorem.

## Hostile counterexample and checks

1. Raw functions are NOT pointwise equal: ell=4, P empty,
   T={x,y}, Q a 2-clique. Bnew({x})=1, but I({x})=3.
   Yet feasibility and canonicalization agree.
2. Every U subset T, including proper U, must be handled.
   Testing only U=T would prove too little.
3. The complete raw old-column function depends on EVERY old
   original in P, not just a selected shadow.
4. Disjoint P,Q is necessary to preserve old c bits under
   the supportBlockOldColumn if-then-else.
5. The P-to-Q isolation is necessary for max capacity; a
   mixed old/reserved clique can otherwise exceed the max.
6. Count vectors may contain repeated copies of a sort; sums
   of multiplicities rather than support cardinalities matter.
7. The proof works for raw zero bounds and the truncation
   a>=ell. Positivity is needed only if claiming a *genuine*
   admissible age, not for set/canonical equality.
8. It uses the global normalized integer witness space; it
   does not assume a fixed finite future W realizes every vector.
9. No new primitive canonicity axiom. The canonicalizer remains
   exactly the verified finite supremum over witnesses.
10. No false Bnew=ideal equality at proper sub-supports.
11. If Q is not a clique, use its genuine clique capacity,
    not its cardinality.
12. A physical reserved stage with arbitrarily many intervening
    originals also needs neutral padding to assign zero
    future columns to all skipped originals. That is independently
    verified by PR #173; this theorem treats the P∪Q pool.
13. The stage must still check complete real Henson old-neighbourhood
    certificates and ensure all selected future vertices have
    the specified positive and negative support columns.
14. Auxiliary H+ parameter-closed I1/I2/I3/B3 and common labelled
    source orbit are not implied by ordinary-L canonical equality.
15. Infinite resolved-diary coherence and BRD bounds remain open.
16. Empty supports are not graph-age coordinates. The
    IntegerGraphSupport subtype enforces nonempty U; no vacuous
    age coordinate is added.

## Lean acceptance

Create Kk/IsolatedSupportCanonicalAge.lean, with explicit
source-witness-equivalence, equality of raw-feasible sets,
canonical equality, canonical block congruence, and exact
age-cover corollary under the genuine cover hypotheses.

Run new-module compilation, fully-qualified strict
standard-only transitive-axiom reports and the complete
repository lake build at the exact PR head. No changes
to Kk.lean, scripts/check_axioms.lean, docs/validation.md,
kk.tex, validation.tex or protected black manuscript prose.
