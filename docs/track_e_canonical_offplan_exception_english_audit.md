# Track E E54 — canonical finite support of physical off-plan exceptions

**English-first, 15 November 2026.** This note precedes any Lean source. It is an
adversarial correction to the arbitrary-Allowed interface in E51–E53, not an
assertion of a uniform big Ramsey bound.

## New mathematical contribution

Let X⊆Y be genuine Kpt seeds in **one** normalized admissible
successor tree, and R,Q their actual AlgorithmRuns with oldTop≤newTop
and a **real** old-top seed. The two physical complete pre-cut
sources are

    ZR(c)=closure_(R.I(c+1))(X),
    ZQ(c)=closure_(Q.I(c+1))(Y).

At each cut c<oldTop choose **independently** two *exhaustive*
finite live indices of the actual sources, with exact membership
equivalences. They may use entirely different finite carriers.

For a single c, define QUIET(c) to mean simultaneously:
* each live *new* Kpt node terminal at level c has **some** live
  old terminal node of level c; and
* each pair (T,U) occurring as the complete old/upper dependent
  L+ ancestors of **one** live new Kpt node occurs as the same
  complete pair of **one** live old Kpt node.

The second item is *relation inclusion* for the existing
IndexedPhysicalCrossing, not node-wise equality or a bijection.

### Lemma 1: index criterion is *equivalent* to physical no-novelty

Suppose the two indices exhaust ZR(c),ZQ(c), **exactly at c**. Then

    QUIET(c)  iff  NewRootNoNoveltyAtCut(ZR(c), ZQ(c), c).

Proof, forward: exactness transports a live new terminal to a
terminal in ZQ(c), and the finite terminal cover transports it
back to a terminal in ZR(c). For crossings, the checked theorem
indexed_physical_crossing_eq_full_closure_relation identifies
the complete pair sets, so finite relation inclusion implies
physical relation inclusion.

Backward: any live new terminal belongs to ZQ(c), hence the
physical I1 implication supplies an old terminal in ZR(c).
Exactness of the old index supplies a live old terminal. For
each full live new pair, equality of the indexed and physical
crossing relations makes it a physical new pair; physical
inclusion gives an old physical pair; exactness reconstructs a
single live old Kpt index realizing *both* dependent types.
This reconstruction retains all auxiliary E/negative-L atoms and
all alternatives at I2 forks. No common node indices are chosen.

### Lemma 2: a canonical minimal finite set of exceptional cuts

Define

    Bad(R,Q) = { c<oldTop :
      c is not selected at stage c by R AND NOT QUIET(c) }.

Because c lies in a finite interval, Bad is a finite **set of source
coordinates**. Equivalently it is a Finset filter of range oldTop
by old-boringness and failure of QUIET.

By unpacking the original two-index off-plan predicate,

    KptTwoIndexOffPlanNoNovelty(..., Allowed,...)
       iff Bad(R,Q) ⊆ Allowed.

This is a necessary AND sufficient criterion. In particular,
Bad is the *least* allowed set admitting the finite no-novelty
tests. The proof uses no fact about the resolved diary, no
counting theorem, and no assumption that Bad is uniformly
bounded in terms of its macrodiary.

### Lemma 3: independence from finite index choices

For two different pairs of exact live finite indices of the
**same** physical ZR(c),ZQ(c) at all c<oldTop, Lemma 1 gives
both QUIET predicates equivalent to exactly the same physical
no-novelty predicate at each c. Hence their finite Bad sets
are **equal**. No matching of their finite indices is needed.

This is useful because the old and bare new roots may have
different parameter closures and multiple finite enumeration
choices, yet the support of genuine physical novelty is
intrinsic to the resulting source configurations.

### Corollary: unconditional finite-support sandwich

The original E52 theorem applied to Allowed=Bad yields

    R.I(i) ⊆ Q.I(i),
    {q∈Q.I(i):q≤oldTop} ⊆
      R.I(i) ∪ {q∈Bad:i≤q}

for i≤oldTop. The word **unconditional** here means only that
no arbitrary off-plan mask is supplied; the statement STILL
requires true nested Kpt seeds, genuine AlgorithmRuns, a real
old-top seed, and two exact finite indices. The support itself
depends on the physical realization and can grow with the
numerical source. **No diary-uniform cardinality bound** follows.

## Tests to prevent overclaiming (16 hostile cases)

1. Old/new source sets genuinely nested in the *same* Kpt tree;
   an isomorphism of graph reducts is insufficient.
2. If the old top is merely a horizon marker, do not apply the
   crossheight theorem without a physical seed at that level.
3. New selected levels above oldTop are not compared.
4. The canonical Bad set is relative to *source* cut indices,
   not an unnormalized numerical H gap.
5. A new terminal that is matched by any old terminal is not
   a terminal failure, even if its node identity differs.
6. It is invalid to require old/new source-index carrier sizes
   to coincide.
7. A matched old prefix T and old upper U from *different* old
   nodes do not suffice: the pair must belong to one old node.
8. Full auxiliary E is different from the concrete graph edge E.
9. Negative ordinary-L atoms must remain in complete type records.
10. At an I2 fork, the physical crossing relation can be
    multivalued; do not identify it with a function.
11. Real K4 q2 cuts 10/22 cannot be discarded as absent.
12. The Bad set may include off-plan cuts with physical novelty
    that are not selected by Q; no converse to E53's selection
    inclusion is claimed.
13. Taking Allowed=Nat makes the old condition vacuous. Our Bad
    is the intrinsic *least* Allowed, not a diary witness set.
14. A bounded number of interesting cuts does not bound the
    number of fully labelled inverse-source orbit types.
15. The bare new initial root is X∪{new original}; ancestor
    closure must be generated by the run, not preinserted.
16. Index-invariance is only asserted **for exact indices of the
    same physical sources**. There is no claim that two
    *different diary occurrences* have the same Bad support.

## Explicit next gap

Find a diary-derived finite planned microevent set P, uniform
over all realized occurrences and with a canonical source-cut
normalization, and prove for every such occurrence

    Bad(R,Q) ⊆ P

as a geometric theorem. Then derive coherent per-event full
dependent L+ assignments and the common labelled inverse source
orbit. The present index-invariance theorem alone proves none
of those statements.

## Validation gates

Implement in a new independent Lean module importing
Kk.PhysicalOffPlanFiniteIndex and Mathlib.Tactic. First compile
the module explicitly; audit every public theorem with exact-head
#print axioms and the strict parser; run the ordinary full lake
build separately. Do not alter black manuscript mathematics or
promote its global pending claims. Do not count an untested new
Lean theorem as validated.
