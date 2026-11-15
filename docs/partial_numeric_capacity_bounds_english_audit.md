# Track A — physical partial-prefix clique-capacity sandwich and ineligible equality

15 November 2026. English mathematics and hostile review **before Lean**.

## Statement

Fix genuine finite numerical-H ordinary binary L associated with
symmetric original graph E; cut before generation g<=k of original b;
finite future selected top-original name family j(t)>b, and any
admissible nonempty support U. Write

  P = {i<b : all U bits E(i,j(t)) positive},
  eligible(U) := all U bits E(b,j(t)) positive,
  N = {z<hPosition(k,b,g) :
       all actual L(z,hPosition(k,j(t),k)) positive}.

Then without pretending that the current original's top copy is
present, the true clique capacity satisfies

  cap_E(P) <= cap_L(N) <= cap_E(P union {b}).

Moreover, if eligible(U) is false, the partial current block
contributes **no U-common neighbour** at any generation and

  cap_L(N) = cap_E(P).

At g=0 the same exact equality holds regardless of eligibility,
by the separately verified complete old-block theorem.

These are genuine original-graph capacities and actual old
numeric-H L capacities, not raw ages with arbitrary invented
future columns.

## English proof

The exact all-support common-pool lemma from parent PR #224 gives
the literal finite set equality

  N = Copies_k(P)
      union (if eligible(U) then {iota(b,q) : q<g} else empty).

The complete real-copy capacity theorem #207 gives
  cap_L(Copies_k(P))=cap_E(P).

Since Copies_k(P) is a subset of N, monotonicity of directed
clique capacity gives the stated lower bound.

For the upper bound, every numbered coordinate in the
right-hand union belongs to Copies_k(P union {b}). This is
literal finite-coordinate containment: earlier original copies
belong because P⊆P∪{b}; a partial current copy iota(b,q)
belongs because q<g<=k and b∈P∪{b}.
Monotonicity yields
  cap_L(N) <= cap_L(Copies_k(P union {b}))
           = cap_E(P union {b}),
where the last equality is again #207. This upper bound
does not require current-original eligibility and is
intentionally weaker than the sharp staircase formula.

If eligible(U) is false, the conditional set on the right
of the exact common-pool identity is empty, so N=Copies_k(P).
The verified complete real-copy capacity equality gives
the exact result, regardless of g.

This is a robust intermediate bridge: the only remaining
sharp phenomenon occurs when b is U-eligible and g>0.
There the exact increase is controlled by
  min(g,1+cap_E({i∈P:E(i,b)=true})),
which requires a separate generation staircase argument.

## Hostile checks

1. Complete future support U is nonempty, to remove odd
   numbered fake H coordinates from N.
2. Numeric current partial copies use q<g<=k; no top b.
3. Multiple current copies cannot be mutually adjacent;
   the upper bound uses the larger *complete* copy pool,
   which is legitimate for a bound but not an equality.
4. All E-clique capacities are maximum CLIQUE cardinalities,
   not counts of vertices.
5. E symmetry is used in #207's exact all-real capacity
   and in the parent's two-orientation column theorem.
6. P need not be an E clique, and its original indices
   need not be consecutive.
7. b is excluded from P because P⊆[0,b).
8. All chosen future j(t) are original indices strictly
   larger than b, but need not be pairwise distinct.
9. A completely ineligible b cannot influence any
   nonempty U-common-neighbour clique capacity.
10. If g=0 even an eligible b has no current-old copies.
11. The upper cap_E(P∪{b}) can be STRICTLY greater
    than the actual cap_L(N); no premature equality is claimed.
12. The capacity inequality is about the fixed true finite
    numerical-H binary-L table, independent of Boolean
    auxiliary Kpt E or closure parameters.
13. The finite graph old prefix can be total Boolean L on Nat;
    physical carrier cutoff remains a separate assumption.
14. The accepted sharp numerical formula has 26,880
    independent cases but no kernel proof here.
15. No stagewise existence of a selected-top original
    realizing a prescribed full original column is asserted.
16. Full auxiliary (I1)--(I3)/(B3), labelled source orbit
    and global big Ramsey degree conclusions are not asserted.

## Lean acceptance

Implement Kk/PartialNumericCapacityBounds.lean on top of
the exact physical common-pool theorem and monotone
finite directed clique capacities. Export the lower/upper
capacity sandwich and the ineligible-current equality;
print all qualified standard axiom reports. Require
direct module build, strict named axiom parser and
full lake build at the exact PR head.

Do not use this as a false replacement for the
sharp non-top generation formula; its role is to
isolate the last staircase inequality needed.
