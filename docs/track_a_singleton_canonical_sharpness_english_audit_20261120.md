# Track A: singleton canonical exactness and sharp canonical event count

20 November 2026 — English-first mathematical proof and hostile audit. This is a new independent finite ordinary-`L` lemma and an extremal construction. It does **not** infer a full dependent `Kpt` interesting-level bound or any BRD claim.

## Theorem 1 — canonicalization does not change singleton raw bounds

Let `ell >= 2`, `d` be finite, `E : Nat -> Nat -> Bool` any directed Boolean graph, `P` a finite old pool, and `c : Nat -> Fin d -> Bool` any complete old-to-future columns. On nonempty admissible supports `T`, define

    B(T) = ell-1 - cap_E({x in P : forall t in T, c(x,t)=true}).

For every sort `t : Fin d`, the singleton support `{t}` belongs to the support domain and

    integerGraphAgeCanonical(d,ell,B)({t}) = B({t}).

**Proof.** Write `r=B({t})`, so `0<=r<=ell-1`. Take `r` formal clique vertices and assign each of them sort `t`; the previously kernel-checked `integerCliqueWeightsOfFinset` produces a normalized clique-weight vector `w` with exactly `r` at `t` and zero elsewhere.

For any admissible `T` not containing `t`, `w(T)=0<=B(T)`. If `t in T`, then the true common-neighbour pool for `T` is a subset of that for `{t}`. Clique-capacity monotonicity gives `cap_E(N_T)<=cap_E(N_{t})`, hence `B({t})<=B(T)`. Therefore `w(T)=r<=B(T)`. The vector is feasible for **every** support, and saturates `{t}`. The canonical supremum is >= r there; the previously verified universal canonical upper bound is <= B({t})=r. Equality follows.

Note that no original Henson freeness, positivity, symmetry, or artificial assumption that every raw age is genuine is required. In particular the proof handles `r=0` and `d=0` (the statement is vacuous when no `t : Fin d` exists).

**Corollary.** For any two physical partial numerical-H cuts `g<=h<=k` against the same given top family, a strict raw singleton drop `B_h({t})<B_g({t})` is exactly a strict canonical singleton drop. Under genuine Henson avoidance the single-step criterion becomes

    G_(B_{g+1})({t}) < G_(B_g)({t})
      iff b is adjacent to j(t), c_{ {t} }=p_{ {t} }=g.

The named singleton `{t}` is genuine because `ell>=2`. This is **not** an analogous result for nonsingleton supports: previously discovered genuine K4 raw-event canonical redundancy (#323) rules out that stronger claim.

## Theorem 2 — the ell-2 canonical-event bound is sharp

For every `ell>=3`, put `d=ell-2`, `b=ell-3`. Take the original vertices:

- `old = {0,...,b-1}`, of size `ell-3`,
- the current original vertex `b`,
- later top original vertices `j(p)=b+1+p`, for `0<=p<d`.

Define an undirected, loopless edge relation as follows:
- all vertices of `old union {b}` form a clique of size `ell-2`;
- each `j(p)` is joined to `b` and precisely the old vertices `0,...,p-1`;
- no two later tops are adjacent; every other edge is absent.

**K_ell-freeness.** A clique meeting no future top has size <=ell-2. A clique meeting a future top `j(p)` contains no other future top, and is contained in `{j(p),b} union {0,...,p-1}`, hence has size <=p+2<=ell-1. Thus the entire graph is K_ell-free. Isolated additional originals, if needed, can extend it to a total graph on Nat without introducing forbidden cliques.

For singleton support `U_p={p}` we have

    P_{U_p}=S_{U_p}={0,...,p-1},
    p_{U_p}=c_{U_p}=p,
    E(b,j(p))=true.

The exact **physical** numerical-H one-jump formula therefore gives:

    B_g(U_p) = ell-1-p       if g<=p,
               ell-2-p       if g>=p+1,

for partial cuts `0<=g<=k` with `k>=ell-2`. By Theorem 1 these equalities hold for the CANONICAL singleton coordinate. In particular for each `p=0,...,ell-3`, the canonical age changes at `p -> p+1`. These are `ell-2` **distinct** generation transitions.

The existing sharp-Henson critical-generation upper bound proves there can never be more than `ell-2` such transitions, regardless of the number of sorts. This construction attains that bound.

This establishes a strictly changing canonical-age chain of `ell-2` transitions in one original H-block, **not** that each transition is a cover in the full graph-age lattice, and **not** the number of full-Kpt interesting levels.

## Hostile checks

1. The singleton tightness proof requires all-support feasibility, which is explicitly constructed; it does not infer feasibility solely from saturating one raw bound.
2. Monotonicity is in the direction `N_T subset N_{t}`, thus `B(T)>=B({t})`. Reversing it would make the argument false.
3. The normalized vector has total `r<=ell-1`; no multiplicity >=ell is requested from `Fin ell`.
4. The theorem remains true at raw bound zero; there need not be a genuine positive age below the raw function.
5. The graph construction has no edges between later tops; this is crucial for K_ell-freeness when `ell` is large.
6. At `ell=3`, the old clique is empty; there is exactly one future top, one edge, and one canonical change.
7. At `ell=4`, one old vertex and two future tops produce two distinct canonical change generations. This is a sharper example than an isolated support raw event.
8. All later top originals `j(p)` are genuinely distinct and above `b` in the fixed natural chronology.
9. Extra unused original vertices must be isolated, not freely joined, when extending the finite example to Nat.
10. The partial phase `g=k+1` is deliberately excluded; `k>=ell-2` ensures every claimed generation step lies in the theorem's range.
11. An entire canonical function changes when a singleton coordinate changes; the two ages need not be adjacent covers.
12. No amount of ordinary age sharpness forces I1 terminal absence, I2 meet absence, I3 skip existence, or parameter-closed B3. These remain separately governed by exact physical Kpt terminal and full L+/E crossing data.
13. This mathematical lemma and family are independently checked below but new Lean source must pass a strict exact-head kernel and axiom gate; previous PR #351 17 endpoints remain unverified.

## Computational referee

A separate pure-Python test reconstructs the explicit source graph for ell=3..8, verifies actual maximum clique size ell-1, exact support capacities, and enumerates **all** normalized integer weight vectors feasible at each partial generation. It confirms equality of canonical and raw singleton bounds, and exactly ell-2 distinct canonical-change transitions. This regression is evidence, not a Lean proof.

## Lean implementation interface

Import `Kk.FiniteOldColumnAge` and `Kk.FiniteCliqueIntegerWitness`. Use `integerCliqueWeightsOfFinset` with `s=Finset.range(B({t}))`, constant sort function `fun _ => t`, and `integerCliqueOnSupport_of_finset`. For every support containing `t`, derive `B({t})<=B(T)` by the existing `finiteDirectedCliqueCapacity_mono` on actual common-neighbour pools; otherwise the weight sum is zero. Close with `witnessValue_le_canonical` and `integerGraphAgeCanonical_le_raw`. A companion Henson application uses `trackA_henson_partial_raw_single_step_iff`.

Do not add validation marks or alter frozen black manuscript text until exact-head Lean compilation and strictly standard-only axiom inspection succeed.

## Additional adversarial brute-force audit: arbitrary directed old columns

The independent Python referee also exhausts **12,495** configurations
of finite old directed Boolean edge tables (0--3 old vertices), arbitrary
old-to-future bit columns for two sorts, and ell=2,3,4. It compares
the canonical supremum over **all** globally feasible normalized integer
weight vectors with the two singleton raw bounds in each case. Exactly
**8,652** singleton raw bounds in this audit are zero. No disagreement
appeared.

A first draft of the Python referee incorrectly represented Lean's
`Nat.sub` using potentially negative Python subtraction; that regression
caught empty feasible sets and was corrected to `max(0, ell-1-capacity)`.
The final exhaustive test explicitly includes the saturated-zero case.
This was a test-harness correction, not a change of mathematical claim.

The new single-step Lean corollary
`trackA_henson_partial_canonical_singleton_step_iff`
reduces its conclusion to the existing real physical raw-event iff via
the generic singleton exactness lemma. All three new Lean endpoints
are still awaiting exact-head kernel and standard-only axiom verification.
