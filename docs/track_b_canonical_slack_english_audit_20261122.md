# Track B: exact canonical-slack criterion for positive selected-witness intervals

22 November 2026. **English proof and hostile audit committed before Lean.**

## Problem

The finite physical age-cover history preserves all originals below its
old cutoff but does not identify the actual top-future witnesses from
different finite numerical-H stages. An extension that incorporates their
actual original addresses can have nonzero positive columns, making the
earlier all-zero / zero-critical-count neutrality hypothesis unnecessarily
strong. The desired new statement is an *exact* finite **ordinary-graph
canonical-age** test on the full original prefix. It is not a proof of the
full parameter-closed Kpt/L+/E history or an existence theorem for coherent
selected numerical-H embeddings.

## Theorem: canonical neutrality iff the critical count fits raw slack

Fix arbitrary directed edge table E, ell >= 2, d sorts, a complete typed
column c on ALL original vertices, and old cutoff b. Let

    B_0(U) = finiteOldColumnRawBound E ell d (range b) c U,
    P      = integerGraphAgeCanonical d ell B_0.

Assume **P is a genuine positive normalized integer-witness age**. This
holds for the actual controlled preparation because the computed target
C is genuine and C<=B_0; the canonicalizer is then genuine. Fix an arbitrary
finite interval [b,b+m), with NO assumption that its inserted original
columns are zero. Let

    N_U = originalCriticalCount E ell d b c U m,
    B_m(U) = finiteOldColumnRawBound E ell d (range (b+m)) c U.

The already kernel-verified literal raw telescoping theorem gives, with
natural truncated subtraction,

    B_m(U) = B_0(U) - N_U.

**Claim (exact iff):**

    integerGraphAgeCanonical d ell B_m = P
      iff
    forall nonempty admissible U, N_U + P(U) <= B_0(U).

The right-hand side measures the critical consumption of the old raw
slack B_0(U)-P(U). It permits genuinely positive previously selected
witnesses and does not assume zero critical-original count.

### Proof

The old original pool is contained in the new one, so B_m<=B_0 by
monotonicity of clique capacity. The finite-witness canonicalizer is
monotone under raw-bound inclusion: G_(B_m)<=G_(B_0)=P. This is the
verified general canonical-mono theorem, not a comparison of selected
shadows.

Consequently G_(B_m)=P iff P<=G_(B_m); by the greatest-genuine-age
property, **given that P is genuine**, this is equivalent to P<=B_m:

* if equality holds, P=G_(B_m)<=B_m;
* if P<=B_m, genuine-age maximality gives P<=G_(B_m), and the
  preceding monotonicity gives the reverse inequality.

For each U, B_m(U)=B_0(U)-N_U. Because P(U)>=1, the natural-number
inequality

    P(U) <= B_0(U)-N_U

is equivalent to N_U+P(U)<=B_0(U), even when N_U>B_0(U).
This proves the iff. It uses no K_ell-freeness of the enlarged original
pool: the raw telescope is valid for arbitrary E. The positivity of P is
**essential** to this strong direction with truncated subtraction.

## Corollary: no unrecorded ordinary canonical drops in the interval

If the slack inequalities hold for the final cutoff, then for every
0<=h<=m, the complete canonical age at b+h equals P.

Indeed the chronological raw bounds are pointwise decreasing,
B_m<=B_h<=B_0, hence their canonical ages are sandwiched between
G_(B_m)=P and G_(B_0)=P. This does not conclude that parameter-closed
Algorithm 5.4 Kpt I1/I2/I3/B3 cuts are boring.

## Exact conditional replacement of the two-stage zero-critical bridge

The existing
`henson_leftDense_second_cover_after_preserved_typed_neutral_gap`
assumes zero critical count throughout the interval [F0,F0+m).
Its proof first gets the next canonical age from that zero-count
hypothesis, then invokes the physical one-cover Henson constructor.
Replace this premise by the strictly weaker exact all-support slack
certificate

    originalCriticalCount(E,ell,d,F0,cNext,U,m) + middle(U)
      <= finiteOldColumnRawBound(E,ell,d,range F0,cNext,U).

Because the old complete columns are preserved and their canonical
age is the genuinely covered middle age, the theorem above derives
canonical age 'middle' at F0+m. Invoke the SAME verified one-cover
physical construction at the enlarged cutoff. The new block is
mutually nonadjacent to ALL earlier originals, including an arbitrary
finite set W0 of previously selected original images, and it preserves
the genuine typed columns of W0, even when positive. Both stage-local
numeric-H witnesses remain actual, but are not asserted to have a
single shared embedding.

## Explicit K4 witness that zero critical counts are NOT necessary

Take ell=4, d=2, old originals {0,1,2,3}, with only ordinary edges
{0,1} and {2,3}. Give 0,1 column (1,0) and 2,3 column (0,1).
The old raw bounds for {a},{b},{a,b} are (1,1,3), while the genuine
canonical age is (1,1,2). Add original v=4, isolated from all four old
originals, but with future passing column (1,1). The resulting raw
bounds are (1,1,2), canonical age still (1,1,2). Thus the raw age
drops by one and v is critical on the *pair* {a,b}, yet the canonical
age is unchanged. The sole critical unit consumes exactly the pair's
one unit of raw slack. The underlying ordinary graph is K4-free.

## Hostile audit: accepted and rejected strengthenings

1. The raw table B_0 need not be a genuine age; in the example its pair
   value is inconsistent with the singleton bounds. Never assume B_0=P.
2. Conversely P must be genuine/positive. A raw bound with all entries
   zero could have unchanged zero canonical values despite critical
   count exceeding its raw bound.
3. The final interval need not be K_ell-free for this algebraic iff.
   Actual Henson application separately provides K_ell-freeness.
4. The statement concerns all nonempty *admissible* supports, including
   mixed and maximal supports, not only selected singleton and pair
   shadows. Outside-domain supports are never evaluated.
5. Every genuine original between the cutoffs participates in the
   literal critical count. Omitting enumeration gaps or old parameter
   originals would falsify the condition.
6. The whole prescribed column c is retained. No prior positive
   passing column is silently zeroed, and the old graph edges E do not
   change.
7. Criticality is defined using complete E mutual adjacencies and the
   whole old common-neighbour pool at the actual preceding cutoff.
   Neither selected-cardinality counts nor one-sided links suffice.
8. The 'raw zero-count necessary' converse is FALSE, as the displayed
   K4 example demonstrates. Canonical slack is the correct budget.
9. A tight raw support, B_0(U)=P(U), allows NO critical insertions if
   the canonical age is to stay fixed.
10. The interval theorem is pointwise and finite; it does not build
    the prescribed selected image set W0 or prove its passing columns
    satisfy the slack budget. That is now the genuine existence gap.
11. All intermediate **ordinary canonical** ages are frozen if the
    endpoint age is unchanged. An auxiliary Kpt microcut can still be
    interesting; the known K4 B3 counterexample is not erased.
12. The derived second-cover physical stage is conditional on fixed
    Henson avoidance and explicit OnePointLeftDense, on the actual
    first stage, and on a genuine next age cover. Its two stage-local
    numerical-H witnesses need not coincide, and it makes NO common
    labelled inverse-source orbit claim.
13. If the last raw support has already dropped to zero, positivity
    of P makes neutrality impossible; the arithmetic proof cannot
    erroneously hide further increases behind truncated subtraction.

## Lean plan

1. Prove the exact all-support canonical-neutrality iff from the
   already checked raw critical-count telescope and canonical-mono
   and canonical-greatest theorems.
2. Prove canonical-age rigidity for every intermediate cutoff and a
   sharp 'tight support cannot be critical' obstruction.
3. Compose with the existing physical two-cover theorem, replacing
   the old zero-count input by the exact slack criterion. Verify the
   resulting witness/prefix clauses with one transitive standard-axiom
   gate. Only then annotate the olive manuscript text.
