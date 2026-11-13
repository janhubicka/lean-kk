# Track C: finite numerical-H+ top-source record — English proof and hostile audit

**13 November 2026.** English-first proof, before the corresponding Lean module.
Parent task: [KK Track C / issue 25](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/issues/25).
This note establishes a *restricted, exact* source record and a conditional
parameter-closure propagation theorem. It does NOT claim the full dependent
source of every Algorithm 5.4 crossing.

## C1. Complete finite top-original L+ record

Let e : Nat -> Nat -> Bool be symmetric, let k>0 and j>0, and let
A = finiteNumericH (normalizedGraphModel e) k N. Assume that the real
top-generation coordinate t = hPosition k j k lies inside the actual
finite carrier (t<N). Put c = hPosition k (j-1) k + 1.

Then, simultaneously:

* **ALL numerical incoming E coordinates, including fake ones**:
  A.E u t = true if and only if u<c, for EVERY natural number u.
* **Canonical free cut**: A.freeLevel t = c. In particular c is the
  first numerical coordinate excluded from the incoming E column.
* **EVERY older original in EVERY generation**: for every i<j and q<=k,
  r=hPosition k i q lies in the finite carrier and the complete
  directed ordinary-L columns are
  A.L.binary r t 0 = e i j and A.L.binary t r 0 = e j i.
  Furthermore A.E r t = true. The E incidence does not depend on
  whether the underlying e(i,j) bit is true or false.

No hypothesis that e itself avoids K_ell is required for these
coordinate identities. It will be required later when the finite
source is declared an admissible Henson/Kpt source.

**Proof.** The literal generated-E formula for a real top target,
together with the finite target-in-carrier restriction, proves the
first equivalence. Uniqueness of canonical free cuts proves the
second statement. For i<j the numerical-coordinate comparison
r<=hPosition k (j-1) k shows r<c and r<t<N. The full
generation-to-top H binary rule has an always-open gate for q<=k;
the forward L bit is exactly e(i,j), and base symmetry transports the
reverse bit to e(j,i). The E equivalence applied to r yields the
positive incoming E bit. This covers generation zero but makes no
claim that its free level is positive.

## C2. Actual selected generation-one source in lower closures

Now let k>1, 0<i<j, and take the same finite numerical H+ structure
A with t<N. Fix any normalized forbidden family which A.L genuinely
avoids, a Kpt seed set X containing the genuine top original at t, and
an AlgorithmRun R on X of height H. Put s=hPosition k i 1 and assume
s<H and that the **actual run** selected s, i.e. s belongs to R.I s.

Then s belongs to the finite carrier, its own free level is positive,
and s<A.freeLevel t. For EVERY p<s, the genuine Kpt original at s
belongs to the FULL meet-and-parameter closure of X at level set
R.I (p+1). This is a source membership statement about the actual
dependent Kpt node, not just an E-positive adjacency.

**Proof.** Strict separation of original blocks gives s<t<N.
The actual numerical H generation-one free-level formula is positive
because i>0 and k>1. The exact top E column gives s<A.freeLevel t.
Run-tail monotonicity transports the already selected s from R.I s
into R.I(p+1). The genuine parameter-closure theorem, applied with
the top Kpt original as a seed and s as selected positive parameter,
puts the original at s into the stated lower closure. This is
precisely the conjunction of the existing physical parameter
lemmas, now exported as one source-record API.

## Adversarial checks (do not suppress any of these)

1. **Fake numerical E positions:** C1 quantifies over *all* u for
   the E column; it does NOT assert that every such u is a Kpt source
   in the parameter closure. Odd fake nodes can matter to corrected B3.
2. **Auxiliary direction:** incoming A.E(r,t)=true does not imply
   A.E(t,r)=true. The source data are directed.
3. **L vs E independence:** even an e-nonedge between genuine
   originals can have a positive incoming auxiliary E incidence.
   One cannot use E-positive to infer L-positive.
4. **Gated L:** C1 works for later top generation only. For a
   non-top later generation, the H gate can drop a positive base edge.
5. **Carrier:** t<N is essential. The finite E constructor is false
   on out-of-carrier targets; do not replace it with the infinite
   generated-E statement.
6. **All earlier generations:** the C1 old-real clause includes
   q=0 and q=k. It says nothing about fake-to-top L columns.
7. **Actual AlgorithmRun:** C2 requires R and s in R.I s; mere
   E-positive incidence or an arbitrary selected-shadow condition
   is insufficient.
8. **Seed and avoidance:** C2 needs a genuine top Kpt original in
   the *same* X, and avoidance for *the same* finite A.L and family.
9. **Positive parameter:** C2 excludes i=0 and uses k>1.
   No assertion is made that generation-zero originals are eligible
   positive parameters.
10. **Lower-cut quantifier:** C2 gives membership in the closure at
    R.I(p+1) for each p<s, not arbitrary future runs or cuts p>=s.
11. **K4 regression:** the actual K4 numerical-H AlgorithmRun
    selects cuts 22 and 10 and carries the genuine generation-one
    original at 22 into the source closure at cut 10. This disproves
    any rule that all auxiliary gadget microlevels are boring.
12. **Assigned upper types remain open:** the full source needed for
    corrected (B3) is the ENTIRE family of crossing Kpt types with
    their prescribed upper L+ extensions, including possible fake
    nodes. C1 and C2 do not identify all those nodes or prove
    agreement of source records across two occurrences.

## Acceptance and next C obligations

In `Kk/NumericHFullClosureSource.lean`, export one C1 theorem giving
all the displayed data without an abstract substitute graph, and one
C2 theorem giving the actual selected source together with positive
free-level eligibility. Require a direct module build and exact
standard-only `#print axioms` checks before marking either Lean endpoint
validated. Keep the manuscript's 112 GREEN / 40 BLUE / 12 PENDING
baseline intact until integration owner G updates provenance.

Next, extend beyond the top seed and generation-one original:
classify **every** parameter/fake Kpt crossing source, attach
`partialTypeAt p` and `partialTypeAt (p+1)` assignments at
every cut, compare the complete I1/I2/I3 records, and only then
hand the full-source theorem to Track D and Track E.
