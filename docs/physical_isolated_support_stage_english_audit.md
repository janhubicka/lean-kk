# Track A — a genuine finite positive support-T stage with every intervening gap accounted for

**14 November 2026. English proof and hostile audit before Lean.**

This follows two already merged, kernel-checked Track A theorems:
(1) the exact literal raw old-column update of an isolated reserved Q
(merged PR #179), and (2) the one-f/M uniform finite numerical-H
ordinary-L realization theorem (merged PR #169).
It does NOT assume the recursive resolved diary exists.

## Finite geometric problem

Let E be the unchanged normalized symmetric/irreflexive left-dense
Henson graph, ell>=2, d>=1, an entire old ORIGINAL prefix
P=[0,b) and an arbitrary total old-to-sort column function
c:Nat→Fin d→Bool. Fix an admissible NONEMPTY support
T∈IntegerGraphSupport(d,ell), and r<ell (for an intended
selected positive join to a full reserved r-clique, the stricter
r<ell-1 is needed; the finite universal age may simply forbid
some future types when r=ell-1).

First use the checked `henson_leftDense_exists_reserved_originals`
to choose one genuine reserved clique Q of size r whose
actual original indices all lie at/above b, with every q∈Q
isolated from every earlier original outside Q in BOTH directions.
The reserved original indices need not be consecutive.

Set
  F = max b (Q.sup id + 1).
Then every q∈Q lies in [b,F) and all real gaps
G=[b,F)\Q remain part of the genuine old Henson prefix.

Define the complete old-to-future column on EVERY p<F by
  C_F(p,t) =
    if p in Q then decide(t in T)
    else if p<b then c(p,t)
    else false.

All old p<b retain the original columns; every reserved q∈Q
sees precisely T, including zeros outside T; every gap
p∈G sees NONE of the future sorts.

## Lemma 1 — exact gap-elimination at the old-neighbourhood level

For EVERY nonempty support U, the common old neighbourhood in
the FULL prefix [0,F) with C_F is literally
the common neighbourhood inside P∪Q with columns
  C_PQ(p,t) = if p∈Q then decide(t∈T) else c(p,t).

Proof: A p in P∪Q has the same entire typed column in
C_F and C_PQ, by disjointness P∩Q and p<b for old p.
Conversely, if p<F lies outside P∪Q, p>=b and p∉Q,
so C_F(p,t)=false for EVERY t. Choose t0∈U
(the support is nonempty) and rule out p belonging to
a common U-neighbourhood. Thus no intervening gap
can accidentally change any old clique capacity.

The equality is of actual finite subsets of the unchanged
Henson ORIGINAL enumeration, not a selected shadow.
It works even if a gap vertex has ORIGINAL E edges to Q,
to the old P, or to another gap; these E edges are irrelevant
to common future neighbourhood because its future columns
are all zero.

## Lemma 2 — exact raw and canonical age with gaps

From Lemma 1,
  B_F(U) = B_(P∪Q)(U)
for every admissible nonempty U, with B defined using the
TRUE E-directed clique capacity of each common neighbourhood.
This is a pointwise raw equality, and hence also equality
after applying the integer graph-age canonicalizer.

The merged PR #179 supplies the literal formula
  rho_F(U) =
    max(rho_P(U), cap_E(Q)) if U⊆T,
    rho_P(U) otherwise.
The positive reserved clique Q has cap_E(Q)=r
because Q itself is a directed clique of size r.

**Important:** B_F is generally NOT pointwise equal to
the IDEAL one-coordinate rawCliqueBlockBound at T:
proper U⊊T may have their raw bounds reduced.
The independent #191 pending proof addresses equality of their
entire feasible integer witness sets and canonical ages.
This lemma does not depend on unverified #191.

## Theorem 3 — a physical uniform finite positive-link future

Apply the already verified theorem
`henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles`
ONCE at the actual expanded prefix F, using C_F.
It constructs one complete compatible finite tagged target,
one genuine pinned original embedding f with f(i)=i for all i<F,
one finite numerical-H carrier M, and one COMMON selected future
W (after F) whose numeric TOP copies realize EXACTLY all
normalized B_F-feasible clique vectors, with no spurious ones.

By the exact raw equality above, the same physical future
realizes all feasible vectors for B_(P∪Q).
Simultaneously the same f,M give:
- every original old p<b at EVERY real generation q<=k
  has L bits to each selected top exactly c(p,tau(w)), both directions;
- every reserved q∈Q at EVERY real generation has L bits
  exactly decide(tau(w)∈T), both directions;
- every real gap g∈[b,F)\Q at EVERY generation has
  ZERO L bits to every selected top, both directions;
- omitted later original indices before a subsequent selected f(w)
  also have zero L bits in both directions;
- odd dummy coordinates have zero ORDINARY L bits (not necessarily
  zero auxiliary Kpt E incidence);
- all selected future top and all old real generations up to F
  lie in the literal finite H carrier [0,M).

One f and one M work for ALL supported clique vectors and for
the old/reserve/gap columns. No positive-column requirement is
hidden as an abstract relative Henson extension axiom:
the finite old+future compatible target was already constructed
and checked by the uniform finite theorem.

## Adversarial checks

1. P=[0,b) must be the ENTIRE old original prefix; the
   old capacity cannot be computed from selected vertices only.
2. Q is an ACTUAL set of original labels, not consecutive new
   abstract indices. F=max(b,sup(Q)+1) records all intervening gaps.
3. Every gap in [b,F)\Q gets a zero future column, including
   gap vertices with arbitrary original edges to Q.
4. Every support U in integer graph-age space is nonempty.
   For U=empty, all gap originals are common neighbours vacuously,
   so the gap-elimination formula would be false.
5. Q is L-isolated from P; without it, the max capacity formula
   after insertion could underestimate mixed old/reserved cliques.
6. The first reserved clique construction is genuinely in the
   SAME fixed Henson graph E, using OnePointLeftDense and the
   forbidden-family avoidance hypothesis.
7. A real selected future adjacent to all r reserved originals
   is impossible when r>=ell-1; the raw feasible profile correctly
   excludes such a future singleton rather than asserting it exists.
8. The uniform target may have no vertices for forbidden
   singleton sorts. It never fabricates positive age coordinates.
9. Do not assert raw B_F=ideal raw cover on proper sub-supports.
10. The *same* f/M is used for profile and old/reserve/gap columns,
    avoiding the invalid conjunction of separate existential witnesses.
11. All L crossing atoms are asserted in BOTH tuple orientations,
    including absent bits outside T and for gaps.
12. Odd dummy ORDINARY L zeros do not settle the auxiliary Kpt E,
    source closure or corrected B3.
13. This is FINITE and cofinal after one reserved insertion.
    It is not a coherent infinite schedule through all diary stages.
14. It does not prove the invariant that the current old reference
    canonical age equals a prescribed upper age. That is a separate
    stagewise Track B obligation; conditional canonical cover
    deduction belongs to the independent #191 theorem.
15. No global BRD numerical claim follows without all-source
    orbit, occurrence factorization and upper/lower arguments.
16. d>0 is necessary for the existing total target sort map;
    no element of Fin 0 is fabricated.
17. k can be zero: the future is then at generation 0, with
    the literal top-to-top gate and carrier bounds.
18. F may equal b when Q is empty; the stage specializes to
    the previously checked uniform finite original future.

## Lean acceptance

New independent `Kk/PhysicalIsolatedSupportStage.lean`, on
current integrated main (it does NOT import pending #191):
- `supportBlockGappedColumn` (complete physical columns);
- exact positive/raw gap neighbourhood and age equality;
- a one-f,M cofinal conditional Q-stage;
- a fully existential genuine Henson reserved-clique plus
  universal future stage under ell,d,r assumptions.

Explicit new module build, strict fully-qualified
named standard-only transitive axioms and full lake build.
Track G owns central Lean imports, validation marks and
protected manuscript; no changes to those files here.
