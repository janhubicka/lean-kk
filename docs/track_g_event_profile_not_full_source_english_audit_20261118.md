# Track G adversarial regression — even all-cut complete local event profiles do not identify Kpt source nodes

18 November 2026. Write English FIRST; formalize as a standalone negative lemma.

## Precise statement

Fix one normalized Kpt family and actual admissible Kpt-node set Z.
Suppose actual admissible nodes x≤y, with y∈Z, x∉Z.
Assume Z contains SOME terminal w at level lev(x):

  w∈Z, lev(w)=lev(x).

Set W=Z∪{x}. Then W≠Z, but for EVERY numerical cut c:

  KptI1AtCut(family,W,c) ↔ KptI1AtCut(family,Z,c),
  FullPhysicalClosureCrossing(family,W,c)
    = FullPhysicalClosureCrossing(family,Z,c).

Thus even the *entire sequence* of full terminal-existence
and complete paired raw dependent old/upper L+/E crossing
relations can forget an actual source node. It is the
event-control signature, not a complete labelled source record.

## Proof

1. W≠Z because x∈W but x∉Z.
2. Crossing equality for each c is the already verified
   `full_physical_crossing_ignores_redundant_terminal_ancestor`:
   x≤y and y∈Z make every crossing of x already represented
   by y with exactly the SAME actual complete Kpt ancestors.
   There is no L-only approximation or assumption about E.
3. For terminal existence at c, one direction Z→W is
   immediate. Conversely, a terminal z∈W of level c either
   already belongs to Z, or z=x. In the latter case c=lev(x),
   and the assumed w∈Z at level lev(x) is a terminal for c.
   Thus terminal flags are equal for ALL c.

## Consequences and limits

- Verified G347 says local I1/I2/I3 decisions are the same
  for all c with identical complete event profiles. This
  example shows those signatures cannot identify Z itself.
- Verified G353 may transport the same I/F run across
  source sets satisfying matching profiles *along the run*,
  but that still does not establish equality of inverse-source
  names or one common labelled monoid orbit.
- The hypothesis requires a redundant actual ancestor x, an
  old higher node y covering its crossings, and another
  old terminal at lev(x) to cover the I1 existence flag.
  The theorem does NOT assert every normalized family or
  every actual AlgorithmRun pre-cut closure realizes these
  three nodes. It is a conditional, literal Kpt source-set
  regression. No artificial counterexample to full diary
  characterization is asserted.
- If old terminal flags are absent at lev(x), they detect
  the addition x. If no y≥x in Z, the crossing equality
  need not hold. Both hypotheses are mathematically needed.
- A per-cut complete profile forgets node multiplicity and
  coherent identity across different cuts; the eventual
  resolved diary must retain sufficient assignment/history
  for each used dependent parameter, not just local spectra.

## Hostile audit

1. x≤y is actual LevelTree order, not ordinary-L adjacency.
2. Both x,y,w are admissible genuine Kpt nodes in the SAME tree.
3. Terminal-cover w need not equal x and cannot if x∉Z.
4. No assumption of literal full-source closure of Z or W;
   do not claim they arise as two AlgorithmRun closures.
5. Full crossing equality holds for all c by the exact
   ancestor restriction theorem, including auxiliary E.
6. I1 asks only existence of a terminal at the level;
   identity and multiplicity are intentionally invisible.
7. I2 same-component pair data is not directly retained;
   G347 only equates the combined I1∨I2 decision.
8. Equality of event decisions does not imply equality
   of minimal envelope embedding types for disjoint X,Y.
9. A canonical chosen source operation need not ignore x;
   total monoid actions outside the observed carrier may differ.
10. This is NOT a lower-BRD colouring, unbounded event-budget
    obstruction or proof the intended refined diary fails.
11. If x∈Z then the inequality conclusion is false, so
    x∉Z must remain an explicit hypothesis.
12. If lev(w)≠lev(x) the terminal flags can differ;
    preserve the equal-level premise.

## Lean acceptance

Import the verified Kpt full physical terminal classifier and
`PhysicalCrossingTerminalBlindness`. Prove the all-cuts
full-profile equivalence and a distinct-source conjunction.
Dedicated exact-head module build, two named standard-only
axiom reports, negative parser self-test and independent full
Lean gate. Do not put this in the frozen manuscript as a
counterexample to the global characterization.
