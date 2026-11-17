# Track A — physical ordinary-L partial age stabilizes after generation ell-1

17 November 2026. English mathematical proof and adversarial review
committed BEFORE Lean.

## Exact statement

Fix a symmetric original Boolean graph E, numerical-H height k,
current original b, given later original top names j(t)>b,
numerical finite Boolean model cutoff M, and integers

    ell-1 <= g <= h <= k.

Let Raw_x be the TRUE numbered partial old binary-L graph-age
function at cut hPosition(k,b,x), against the SAME future top
name family j(t) for all nonempty IntegerGraphSupport d ell.

Then the entire total support functions are identical:

    Raw_g = Raw_h.

Hence also:

    integerGraphAgeCanonical d ell Raw_g
      = integerGraphAgeCanonical d ell Raw_h,

and the corresponding feasible integer clique-multiplicity families
are exactly equal.

This is a universal finite conditional statement, not an assumption
that a recursively prescribed selected name family has been realized.

## English proof

The verified physical old age antitonicity (PR #228) says

     Raw_h(U) <= Raw_g(U)

for every nonempty admissible support U.

The exact raw support event iff, verified in PR #284, says a strict
inequality Raw_h(U)<Raw_g(U) could occur ONLY if

     g <= p_U < h and p_U < ell-1,

where p_U is the original earlier U-common-neighbour clique capacity.
But g>=ell-1 contradicts these inequalities. Therefore strict
inequality is impossible for every U, and the antitonicity implies

     Raw_h(U) = Raw_g(U).

Function extensionality gives total raw function equality.
The canonical graph age and feasible normalized integer clique
vectors are functions of this raw bound alone; applying them to
equal arguments gives equal outputs.

No positivity or raw-age-cover assumption is introduced.

## Adversarial checks

1. The partial cuts satisfy g<=h<=k. At g=k+1 the current
   original b TOP copy enters and the top-top generation
   gate changes; the theorem does NOT cover that transition.
2. The threshold is exactly ell-1 (Nat truncated subtraction),
   not ell and not ell-2.
3. ell=0 and ell=1 are allowed mathematically; all relevant
   raw support values are zero, so the theorem is consistent.
4. If ell-1>k, the hypotheses are inconsistent, so the statement
   is vacuous rather than supplying nonexistent physical levels.
5. The original E and chosen future top original names j(t)
   are FIXED across the cuts, not re-chosen stage by stage.
6. Every numbered old coordinate, including intervening odd
   fake vertices, remains in the genuine old source pool.
   Their U-crossing behaviour was already kernel checked.
7. The raw support domain is all admissible NONEMPTY U;
   no inference from singleton supports is sufficient.
8. No finite carrier membership is claimed unless numeric
   cutoff M also contains old/future top positions.
   The Boolean binary L table calculation is total on Nat.
9. A canonical age cannot change when the entire raw support
   function is equal, regardless of nontrivial canonicalization
   constraints.
10. No converse is asserted: earlier partial cuts may also
    have equal ages due to ineligibility, linked capacity deficits
    or truncation.
11. Tail stability is purely ORDINARY L. The true selected
    minimal envelope and parameter-closed Kpt E/auxiliary B3
    records may change at later generations even with constant
    raw and canonical ordinary-L graph ages.
12. No infinite resolved-copy schedule or labelled source orbit
    is constructed, so this alone does not yield BRDs or the
    24-orbit theorem.

## Acceptance

Implement Kk/PartialNumericLateAgeStability.lean with the
verified PR #228 antitonicity and PR #284 raw-event iff as
the only mathematical input. Derive exact raw function,
canonical age and feasible vector equalities. Require
exact-head direct module build, qualified standard-only
named axiom checks and full Lake.

The manuscript may claim only this finite ordinary-L
tail stability after successful CI; full dependent B3
is an explicit TODO.
