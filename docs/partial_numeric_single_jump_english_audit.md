# Track A — exact one-jump ordinary-L age profile at partial numerical-H cuts

17 November 2026. English proof, adversarial checks and scope **before Lean**.

## Reviewed kernel input

The exact-head [PR #256](https://github.com/janhubicka/lean-kk/pull/256),
CI [44033636025](https://github.com/janhubicka/lean-kk/actions/runs/44033636025),
is merged into main with the exact named theorem
`Kk.finiteNumericH_partial_actual_capacity_eq_sharp`.
The full build, named standard-only axiom gate and the independent
26,880-case actual finite numerical-H interpreter passed.

Fix symmetric original Boolean E, height k, old partial cut
`m=hPosition(k,b,g)` with `g<=k`, *given* later original top names
`j(t)>b`, and a nonempty supported U. Define

    P_U = {i<b : E(i,j(t))=true for every t in U},
    S_U = {i in P_U : E(i,b)=true},
    p_U = cap_E(P_U),     c_U = cap_E(S_U),
    eligible_U = for all t in U, E(b,j(t))=true.

The verified sharp formula is

    cap_L(N_U) =
      max(p_U,
         if eligible_U then min(g,1+c_U) else 0),

where N_U is the entire ACTUAL numbered old U-common-neighbourhood
computed from the literal `finiteNumericHL` ordinary binary relation
to those later top originals.

## Main simplification: a single exact threshold

Because S_U subset P_U and clique capacity is monotone, always

    c_U <= p_U.

The nested max/min expression therefore *simplifies exactly* to

    cap_L(N_U) =
       if eligible_U AND c_U=p_U AND p_U<g
       then p_U+1
       else p_U.

Proof by cases:

- If b is ineligible, no b generation enters the old
  common-neighbourhood; the old capacity is p_U.
- If b is eligible but c_U<p_U, then c_U+1<=p_U, so
  min(g,1+c_U)<=p_U for every g and the maximum remains p_U.
- If b is eligible and c_U=p_U, then min(g,p_U+1) exceeds p_U
  if and only if g>=p_U+1, equivalently p_U<g.
  In that case the new value is exactly p_U+1; otherwise p_U.

Thus for each fixed nonempty U and fixed given future top names,
the capacity along 0<=g<=k has at most ONE upward jump of ONE,
at the transition from g=p_U to g=p_U+1, provided
eligible_U, c_U=p_U and p_U+1<=k.

This result is more informative than a monotonicity theorem:
a capacity cannot creep up at two separate generations
inside a single original block. It is independent of the
numerical finite carrier bound M *as a Boolean L-table
calculation*; physical finite-carrier membership still needs
the conventional numeric cutoff constraints.

## The raw, canonical and feasible-vector identities

For the actual complete old physical column at cut g,
the raw future graph-age bound is by verified definition

    Raw_g(U) = ell - 1 - cap_L(N_U)

using natural-number truncated subtraction.
Define `StepRaw_g(U)` by substituting the single-jump expression:

    StepRaw_g(U) =
      ell-1 -
        (if eligible_U AND c_U=p_U AND p_U<g
         then p_U+1 else p_U).

The statement `Raw_g = StepRaw_g` is a pointwise equality
of functions on ALL nonempty `IntegerGraphSupport d ell`,
not just equality at singleton supports. As a result,
applying the actual integer graph-age canonicalizer yields

    integerGraphAgeCanonical(Raw_g)
      = integerGraphAgeCanonical(StepRaw_g),

and the feasible normalized labelled clique multiplicity families
`feasibleIntegerCliqueVectors d ell` coincide exactly.

A capacity jump may be invisible in the raw age when the
subtraction has already truncated to zero; do NOT state
that every capacity jump is automatically a cover event in
the canonical age poset. Even when raw bounds change,
canonicalization can couple distinct supports.

## Adversarial audit checklist

1. S_U subset P_U is proven from the actual filter definition;
   never replace c_U with |S_U|.
2. The original E is symmetric when invoking the verified
   numerical-H capacity formula, but the monotonicity argument
   for c_U<=p_U is purely directed and does not need symmetry.
3. Eligibility is NOT optional. Removing its guard makes
   the equation false for an ineligible current original,
   even in a 3-vertex K4-free graph.
4. The numeric cut excludes all b generations q>=g; g<=k
   excludes b's top generation. At the next completed block
   a separate top-top gate becomes available.
5. g=0 always yields p_U, including p_U=c_U=0.
6. If c_U<p_U, no jump occurs for any g, irrespective
   of the finite H height.
7. If c_U=p_U=0 and b eligible, g=1 yields a singleton
   b-generation clique and capacity jumps from 0 to 1.
8. If p_U>=k, the jump threshold p_U+1 lies outside
   the allowed non-top range g<=k; no partial jump occurs.
9. Future original top names must be GIVEN and later than b;
   their existence under a recursively prescribed original
   E-column is an unresolved separate physical problem.
10. The common-neighbourhood includes all numbered old
    coordinates, including odd dummies; the verified theorem
    eliminates their ordinary-L contribution using U nonempty.
11. Raw bounds use natural truncated subtraction ell-1-cap,
    so a capacity jump need not induce a strict decrease.
12. Canonicalization of integer clique vectors can couple
    supports, so single-support capacity jumps do not by
    themselves classify full cover/boring/interesting events.
13. No claim of source E/auxiliary parameter closure or
    selected-generation B3 agreement is made.
14. The physical finite carrier bound M does not enter
    the RHS, but to speak of finite H *vertices* rather
    than the total binary relation on Nat, both old and
    future top numeric positions must lie below M.
15. Support U is nonempty and admissible (IntegerGraphSupport),
    not an arbitrary empty support; otherwise odd dummies
    may affect the unfiltered pool.
16. Repeated future sort names are permitted by the finite
    theorem, not evidence of a valid future *embedding*.
17. The global resolved-copy upper Ramsey theorem and the
    lower BRD orbit-count characterization still require
    the actual recursive schedule and common labelled source.

## Acceptance criteria

A new standalone `Kk/PartialNumericSingleJumpAge.lean` must:

1. Prove a pure Nat arithmetic max/min single-jump identity
   under `c<=p` and a general decidable eligibility condition.
2. Derive the ACTUAL numerical-H single-jump capacity identity
   directly from the verified PR #256 kernel theorem and
   `finiteDirectedCliqueCapacity_mono`.
3. Define a simple M-independent total raw support function
   `finiteNumericHPartialSingleJumpRawBound` and prove pointwise
   equality to the ACTUAL old-column raw age.
4. Derive exact canonical-age and feasible-vector equalities
   using the existing integer-age API.
5. Run a strict exact-head direct module build, all qualified
   named standard-only axioms, the independent literal-H
   regression and full Lake build.

Only after all steps succeed should the manuscript acquire
a new, narrowly scoped green marker. The global theorem
and full parameter-closed B3 remain PENDING.
