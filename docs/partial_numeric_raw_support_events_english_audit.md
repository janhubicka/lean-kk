# Track A — exact raw-support event criterion between physical partial cuts

17 November 2026. English proof and adversarial review BEFORE Lean.

## Kernel inputs already certified

The original numerical-H height and source model are fixed. For any
symmetric original E, original b, g<=h<=k, arbitrary finite total
numeric Boolean carrier bound M, and given later top original names
j(t)>b, the exact physical one-jump age identity is merged in
Kk/PartialNumericSingleJumpAge.lean, PR #273, tested head
4d4da221e2d89e0b540ec92acc6ebe0e714b7624,
successful CI 44038671507 (direct module, strict named axioms,
26,880-case physical checks and full Lake).

At a nonempty admissible future support U write:

  P_U={i<b : E(i,j(t)) true for all t in U},
  S_U={i in P_U : E(i,b) true},
  p=cap_E(P_U), c=cap_E(S_U),
  eligible=(E(b,j(t)) true for all t in U).

For a partial cut before b-generation x<=k, the genuine numbered
ordinary-L old-support clique capacity is

  C_x = p+1  iff eligible and c=p and p<x,
  C_x = p    otherwise,

and its raw future bound is R_x=ell-1-C_x in Nat, with
TRUNCATED subtraction.

## Precise event criterion

For g<=h<=k the ACTUAL RAW support value strictly decreases,

    R_h(U) < R_g(U),

if and only if ALL of the following hold:

  (i) b is U-eligible;
  (ii) c=p (there is a maximum original P_U-clique linked to b);
  (iii) g<=p<h (the two cuts straddle the unique threshold p+1);
  (iv) p<ell-1 (the original raw age is still positive).

Whenever this strict event occurs, it is exactly a ONE-UNIT
decrease: R_h(U)+1=R_g(U).

Proof: If eligibility fails or c<p, the one-jump capacity is p
at both cuts. In the remaining case, C_x changes from p
to p+1 only when x crosses p+1. The old/new bounds are
ell-1-p and ell-1-(p+1), respectively. By Nat subtraction,
the latter is strictly smaller exactly when p<ell-1.
When it is smaller the difference is exactly one.

This is an iff statement for ACTUAL given future top names,
not a comparison of two independently chosen reference columns.

## Hostile checks

1. The cut indices satisfy g<=h<=k and share **the same** original
   E, current b, selected future name family j, numerical height
   and finite Boolean carrier bound M.
2. If h=g no raw event occurs; the criterion g<=p<h excludes it.
3. If b is not U-eligible its old copies have zero selected U
   crossing and cannot create a support event.
4. If c<p then c+1<=p and no capacity event occurs at any partial
   generation of b, even when g rises far above p.
5. If p>=k the threshold p+1 is outside the partial range and
   there is no event before b's TOP generation is included.
6. If p=0=c and b eligible, the first partial cut with g=1
   introduces the only possible singleton old clique.
7. If ell-1<=p then the raw bound is truncated to zero both
   before and after the capacity event. It is **false** that
   every capacity increment produces a strict raw age decrease.
8. Every raw event is exactly of size one, never a multi-unit
   decrease for one support in one original block.
9. The condition refers to a maximum **clique** in P_U linked
   to b, not the cardinality of P_U or S_U.
10. The formula is evaluated at every nonempty admissible
    `IntegerGraphSupport d ell`, including mixed supports;
    singleton-only verification would be insufficient.
11. Source E symmetry is required for the actual numerical-H
    sharp capacity theorem, not for the arithmetic simplification.
12. Odd fake numerical coordinates are INCLUDED in the literal
    old prefix; their ordinary-L U-crossings are zero as proved.
13. The finite total Boolean binary table calculation is
    independent of M, but literal physical carrier membership
    requires old/future numeric coordinates below M.
14. The chosen later original j(t) must be genuinely later than b.
    The finite theorem does not construct a recursive schedule
    realizing arbitrary prescribed original columns.
15. A strictly changing RAW support bound need not be a
    cover of canonical graph ages. Other supports can impose
    additional consistency constraints and eliminate an
    apparent single-support change.
16. Nor does a raw support event classify the parameter-closed
    Kpt E/auxiliary-dependent (I1)--(I3)/(B3) level.
17. Nothing here establishes a common labelled source across
    different occurrences, diary expansion or global BRD number.

## Lean acceptance

Implement Kk/PartialNumericRawSupportEvents.lean, with:
- the purely arithmetic inequality iff and exact one-unit lemma
  on truncated Nat subtraction of two one-jump expressions;
- the actual physical numerical-H U-support event iff, using
  the independently certified PR #273 raw age equality;
- optionally the one-unit decrease statement for the actual
  physical raw age.

Verify exact-head direct module Lake build, strictly qualified
standard-only named axioms, full repository build, and a separate
independent literal-H numerical finite model that enumerates both
cutoffs, several ell truncation thresholds, and explicitly
checks the iff and unit difference.

Do not promote a canonical cover or B3 statement without additional
age- and source-level arguments.
