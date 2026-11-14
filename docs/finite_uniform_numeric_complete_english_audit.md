# Track A — SAME finite Henson embedding realizes all numeric top profiles and all old/gap columns

**14 November 2026. English-first proof and adversarial audit.**

This final finite *ordinary-L* composition is deliberately stronger than merely conjoining
the two existential conclusions of Track A PRs #161 and #166. Those theorems each say
"there exists f", and two independently chosen witnesses f1 and f2 need not coincide.
A valid composition must reuse **the very same f and finite numerical carrier M**.

The new branch is stacked on the checked numeric-top-source head of #161 and temporarily
includes the **byte-identical, already exact-head-verified** `Kk/FiniteUniformNumericColumns.lean`
source from #166, for compilation before Track G's controlled merge. Do not merge the temporary
duplicate: merge #166 once and deduplicate or rebase this branch before integration.

## Exact statement

Let E be one actual normalized Henson original graph with forbidden-family avoidance and
OnePointLeftDense. Fix ell≥2, d>0, an entire old prefix [0,b), an arbitrary complete
typed old-to-future column c(p,t), and any numerical-H height k.

Compute raw old-column bound B_P(T) from **all** old original common-neighbour clique
capacities. Define the **explicit** finite universal target A (PR #155) and its same
finite named future W; PR #157 proves one pinned physical embedding f, and PR #161 proves
that for ONE choice of f and one finite numerical cutoff M:

1. all old i<b are fixed: f(i)=i;
2. f preserves all off-diagonal ordered L bits in the entire finite target;
3. every new f(w) has both-sided zero adjacency to all earlier omitted original indices;
4. old and selected future top real copies are genuinely within finite numerical-H carrier M;
5. the ONE numerical top pool Q = numericHTopPool k (W.image f) has exact *whole normalized*
   feasible integer clique profile, including no spurious profiles.

Use f and M **as already chosen in PR #161**. The generic checked PR #166 old-column
and omitted-gap lemmas apply directly to the same f because the target A is the
already-verified explicit finite tagged encoding:

```text
for EVERY old i<b, EVERY w∈W, EVERY generation q≤k:
  L^H_{k,M}(iota(i,q), iota(f(w),k))
    = L^H_{k,M}(iota(f(w),k), iota(i,q))
    = c(i,tau(w)).

for EVERY w∈W, EVERY omitted original z<f(w) not in f([0,w)),
 and EVERY q≤k:
  L^H_{k,M}(iota(z,q),iota(f(w),k))
    = L^H_{k,M}(iota(f(w),k),iota(z,q))
    = false.

for EVERY odd dummy 2a+1 and w∈W:
  both ordinary L bits between dummy and iota(f(w),k) are false.
```

These combine **at the same f and M** with Q's complete feasible clique profile.

## Actual finite carrier refinement

The carrier cutoff from PR #161 is above every top coordinate of an old original i<b and
every chosen future f(w). Consequently it contains **every old real generation** q≤k,
because iota(i,q)≤iota(i,k). It also contains every real generation of a skipped original
z<f(w) because iota(z,q)<iota(f(w),k)<M. These strict inequalities are purely numerical
block-order facts, not inferred from the old graph.

All ordinary-L atoms claimed for old or skipped original real generations therefore
represent *actual carrier vertices* of the finite numerical-H structure, not values of
its total extension of L outside the carrier. Odd dummy atoms can be stated as total
Boolean zeros; to claim their physical presence, require 2a+1<M.

## Proof dependencies

- PR #157: one **constructed** compatible finite universal relative graph A and one actual
  pinned original embedding f with all-gap zeros, all feasible vectors.
- PR #161: exact top-to-top E/L identity, finite top clique-profile transfer,
  finite carrier cutoff M and **one** f, M with all top vectors.
- PR #166: generic full old-to-top columns at every generation, genuine omitted-original
  zeros at every generation, odd dummy zeros, with arbitrary previously supplied f.
- The exact tagged old-to-future column lemma from PR #147:
  `A(i,w)=c(i,tau(w))` whenever i<b and w∈W.

No independent Henson realization is invoked in the combined proof: take f,M from PR #161,
derive old/gap columns with the generic lemmas of PR #166, and retain the original f,M/Q.

## Hostile checks

1. **One f:** the principal logical trap is `(∃f,P f)∧(∃f,Q f)` not implying
   `∃f,P f∧Q f`. We reuse PR #161's one f,M and *do not call* PR #166's existential
   corollary to choose another.
2. **Every marked future:** old/gap formulas quantify all w∈W, not just one designated
   support T.
3. **Both ordered arcs:** all c bits and skipped gap zero bits are certified in both
   directions.
4. **All generations:** old and omitted original q may be arbitrary real generation ≤k,
   including q=k; the selected future is at TOP k.
5. **Top graph profile joint:** each feasible vector's count vector is compared across
   every support simultaneously; the finite pool Q is the same for all vectors.
6. **Complete old prefix:** all original indices below b are included, even if they
   correspond to future diary parameter/gap vertices in another representation.
7. **Carrier for omitted gaps:** because each z<f(w), its every real generation occurs
   before the chosen top f(w); the cutoff M includes it. This is stronger than merely
   writing a Boolean equality for an address outside the finite carrier.
8. **No erased selected edges:** skipped-original zero formula only tests indices not among
   f([0,w)); earlier selected target images can have prescribed positive edges.
9. **No auxiliary Kpt E assertion:** real/dummy ordinary L constraints do NOT identify
   full parameter-closed I1/I2/I3/B3 source records.
10. **No infinite stage induction:** f and M are finite and may depend on the initial
    b and c. No fixed countable resolved copy, exact diary count, or orbit theorem follows.
11. **No wrong old-reference cover identification:** the profiles are raw B_P-feasible.
    Proving equality to a prescribed diary state F throughout a recursive stage still
    requires Track B's full reference-age invariant.
12. **No nonempty future assumption:** W may be empty. The top profile then concerns the
    zero vector, M still includes old top copies, and old/gap columns are vacuous.
13. **Literal old and gap carrier bound:** prove numerical inequalities, do not assume
    odd dummy E-incidence vanishes just because its L bit does.
14. **No unjustified original relabelling:** the top map uses actual nonconsecutive f(w)
    indices in the unchanged fixed E, not a renumbered abstract universal graph.

## Lean acceptance

Add `Kk/FiniteUniformNumericComplete.lean` importing
`Kk.FiniteUniformNumericTopAge` and `Kk.FiniteUniformNumericColumns`.
Prove one single theorem exporting one f,M with (1)–(5) above plus complete old/gap/dummy
columns and genuine carrier bounds for all tested real positions.

The new theorem must compile with a strict standard-only fully-qualified transitive
axiom report at the exact feature-head, plus full `lake build`. Track G will deduplicate
the temporary #166 source and manage all central validation marks/TeX. None of the
black manuscript is changed.
