# Track A — actual partial numerical-H common-neighbour pool

**15 November 2026. English mathematical proof and adversarial audit before Lean.**

## Statement (literal physical pool, not its cardinality)

Fix numerical height k, original b, generation g<=k and actual
finite numerical-H ordinary binary L induced from an original
undirected E. Choose any finite family of future **original**
names j(t)>b and an admissible nonempty support U of future sorts.

Define the original common-neighbour set
  P(U)={i<b: for all t in U, E(i,j(t))=true},
and the current-original eligibility condition
  eligible(U) iff for all t in U, E(b,j(t))=true.

The entire actual numbered H old U-neighbourhood at cut
  m = hPosition(k,b,g)
is **exactly** the following union of actual coordinates:

  (all k+1 real generations of all i in P(U))
    ∪ (if eligible(U), then {hPosition(k,b,q):q<g}, else ∅).

This is an equality of concrete Finset Nat vertex addresses, not
just equality of capacities, and it includes all odd dummies in
the left-hand old pool before proving their contribution is empty.
When g=0 the result reduces to complete earlier original blocks.

## Proof

1. The previous partial-prefix theorem computes the actual
   U-common-neighbourhood inside the literal [0,m) as the
   U-common-neighbourhood of the *complete EVEN pool*, using
   the pulled-back original columns. Its proof first proves
   that actual crossings to every given future top original
   equal the pulled-back columns in BOTH orientations, and then
   eliminates odd dummies by U nonempty.
2. The exact EVEN-pool partition from the previous module is
     Even = Copies_k([0,b)) ∪ {iota(b,q):q<g}.
   Hence membership in its U-neighbourhood splits by these
   two source pools.
3. If z=iota(i,q) with i<b, the decoder satisfies
   orig_k(z)=i. The complete pulled-back column is
   E(i,j(t)) for every t, independently of q. Thus z is
   U-common precisely when i belongs to P(U), yielding
   Copies_k(P(U)).
4. If z=iota(b,q), q<g<=k, then orig_k(z)=b.
   Its U-common condition is independent of q and equivalent
   to eligible(U). Thus either *all* q<g copies survive or
   none do. The two components remain disjoint because their
   original names differ.
5. The reverse inclusions use the same exact decoder on
   each bounded coordinate. No projected age lemma is needed.

## Hostile checks and boundaries

- The **nonempty** U hypothesis is indispensable: at U=∅,
  all odd dummy addresses would satisfy the vacuous condition.
- A partial cut is before generation g of b. Its g partial
  copies have q=0,...,g-1, **not** 0,...,g.
- g<=k excludes the present top copy of b. At g=k+1
  the generation gate changes and a separate theorem applies.
- Full real earlier originals i<b include every q<=k, even
  when their original indices are nonconsecutive selected names.
- The future names are **given** and satisfy j(t)>b; this
  result does not construct them in the Henson enumeration.
- Equality uses the *actual finiteNumericHL binary table*,
  not an invented column assignment.
- Odd fake coordinates remain physical H vertices; they
  may have auxiliary Kpt E incidence and should not be erased
  from a full (I1)/(I2)/(I3)/(B3) comparison.
- The original graph is assumed symmetric to identify both
  directed L crossings; no loop is ever needed in the pool.
- Carrier bounds hPosition(k,b,g)<=M and
  hPosition(k,j(t),k)<M remain required for a literal finite
  substructure interpretation; the Boolean tables themselves
  are total on Nat.
- Repeated future sort names do not invalidate pool equality,
  although they would prevent a future set of distinct vertices
  if injectivity were required elsewhere.
- All nonempty supports U of arbitrary finite type width d
  are included, not just singleton U.
- The theorem does **not** assert the sharp maximal clique
  formula yet. That additionally needs injective projection
  of mixed-generation cliques and the generation staircase bound.
- No full selected-front canonical cover event or auxiliary
  source matching is inferred from this exact pool.
- The previous independent interpreter covered 26,880
  four-original cases and checked the same pool identity,
  but this Lean theorem is the actual universal proof goal.

## Lean plan / acceptance

Use Kk.PartialNumericOldColumns (the source exact physical
column and even-pool partition module), the established
numericHCompleteRealPool_mem_iff and
numericHRealOriginal_at decoder. Prove both directions by
Finset.ext and cases on the two real-pool sources; factor
the support condition using the exact decoder. Import only
existing modules, add independent Kk.PartialNumericCommonPool
with its own qualified #print axioms and dedicated exact-head
CI. Do not modify frozen manuscript black text or promote
its global pending claims. Remain DRAFT until both the
parent #221 and this module compile with standard axioms.
