# Track G — actual ancestor action of a genuinely boring block

18 November 2026. English proof FIRST, before Lean. New purpose: obtain a
genuinely local, source-level overlap comparison of **different** actual
AlgorithmRuns without pretending that their total monoid maps agree.

## Proposition A (ancestor action, not just factorization)

Fix an actual run R: AlgorithmRun H X top and 0<=low<=high<=top.
Assume EVERY i in [low,high) is boring for the **complete** actual
parameter-closed source closure(H.S, R.I(i+1), X), not merely its
selected ordinary-L graph-age shadow. Then there exists a UNIQUE
total D:MMap H such that

  F_R(low) = F_R(high) o D,

and for EVERY actual Kpt/tree node c in closure(H.S,R.I(high),X)
of level at least high, we have

  D(ancestor(c,low)) = ancestor(c,high).

These are genuine total MMaps / actual Kpt ancestors, not quotients
or graphical interpretations. No E1, bounded source size, or
fresh-origin assumption is required: the actual run already supplies
the one-step crossing requirement.

Proof: finite downward induction on i from high to low.
At i=high choose D=id; the ancestor statement is reflexive.
At a boring i, the verified noninteresting_step supplies Di in M
with F(i)=F(i+1) o Di, and on every c in
closure(S,R.I(i+1),X) of level >i,
Di(ancestor(c,i))=ancestor(c,i+1).
The verified G305 all-boring interval lemma on [i+1,high)
gives I(i+1)=I(high), so the stated fixed c belongs to the
actual pre-cut source at this step. The induction factor E
has E(ancestor(c,i+1))=ancestor(c,high) and
F(i+1)=F(high) o E. Take D=E o Di; associativity holds
pointwise for actual MMaps, yielding both requested identities.
Uniqueness of D is G309's injective left-cancellation by F(high).
No uniqueness of the individual choices of skip map Di is needed.

## Proposition B (same-coordinate physical overlap of two runs)

Let R:AlgorithmRun H X topX and R':AlgorithmRun H Y topY
be TWO actual runs in the SAME underlying successor tree.
Assume low<=high<=min(topX,topY) and every cut of [low,high)
is genuinely boring in EACH run on its OWN full source.
Let D and E be their respective unique accumulated factors.
Then for any literal actual tree node c in the INTERSECTION

  closure(S,R.I(high),X) ∩ closure(S,R'.I(high),Y)

of level >=high,

  D(ancestor(c,low)) = E(ancestor(c,low))
     = ancestor(c,high).

Proof: apply Proposition A separately to R and R'. Each
factor takes the SAME actual lower ancestor of the COMMON
physical node c to its SAME actual upper ancestor. No
equalities of total maps F_R,F_R' or selected I-level sets
are required, and X,Y may be different.

## Stronger conclusion and precise obstruction

The relevant **restriction** of the boring factor to lower
ancestors of literal common complete Kpt source nodes is uniquely
determined by the underlying physical node and the common cut
coordinates, despite arbitrary choices of skip-only MMaps.
This is more useful than G318's unconditional factorization:
it gives a concrete cross-run action equality on the physically
shared source, without claiming all total D,E are equal.

However it does NOT compare two disjoint diary occurrences:
a physical Kpt-node identification with complete L+/E atoms
and an order-compatible cut-coordinate map would still need to be
constructed. It also does NOT bound the number of boring cuts or
the labels encoded by total D,E outside the literal shared carrier.

## Adversarial checks

1. The full actual pre-cut closure is essential. Selected-front
   age equality does not imply all-boring (K4 q1=10, q2=22).
2. The fixed source node has level >= high, so every relevant
   ancestor(c,i) is defined and i<level(c) at step i<high.
3. The inner interval [i+1,high) is also genuinely boring;
   applying G305 there identifies the *complete* I sets.
4. The step closure is exactly closure(S,R.I(i+1),X); no
   ancestor-prefix closure of X itself is postulated.
5. The whole crossing equation is for ONE node c and the
   actual monoid witness Di; no old/upper L-reduct simplification.
6. The composition order is E o Di, not Di o E.
7. At i=high the identity is the unique endpoint factor;
   the statement allows the empty interval low=high.
8. The proof of uniqueness uses F(high) injective and equality
   as total MMaps, not just equality on marked ancestors.
9. Two runs may have different X,Y and different top heights;
   only the common numeric interval and same underlying tree
   are required in the overlap lemma.
10. Each run is assumed *independently* fully boring; one run
    being boring does not imply the other is boring.
11. No global equality D=E follows: the factors can differ
    away from the common ancestor set, even if that set is nonempty.
12. The overlap may be empty, so Proposition B is NOT a common
    source existence theorem; a genuinely new carrier is needed.
13. Different cut-coordinate maps require additional transport;
    the current proof assumes literal identical low/high.
14. Preservation of the actual upper dependent L+/E successor
    assignments between different nodes is NOT proved.
15. K4 selected microevents 10 and 22 are not compressed away;
    they violate the all-boring hypothesis if in the interval.
16. No bounded interval length, bounded labelled factor complexity,
    common inverse Kpt orbit, resolved infinite H+ copy, (B3)
    relative-continuation equality, or BRD theorem follows.

## Lean acceptance plan

Commit this mathematical proof first. Then implement A by induction
using only G305 and G309/G318 existing actual-run API and the genuine
one-step ancestor crossing law. Implement B by two applications of A.
Directly compile source and check two exact qualified #print axioms
under the strict parser self-test on the PR exact head, plus full Lean
CI. Keep these scoped components separate from central Kk.lean until
checked, and do not edit black manuscript or green global markers.
