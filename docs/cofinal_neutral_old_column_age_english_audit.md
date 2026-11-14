# Track A — cofinal neutral padding preserves the complete old-column age

**14 November 2026. English proof and hostile audit BEFORE Lean.**

Base: `lean-kk/main` after merged Track A PR #169
(`henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles`).
This standalone Track A continuation does NOT change existing Lean
proofs, central validation registers, or frozen manuscript prose.

## The exact scheduling problem

The finite uniform relative-Henson realization theorem fixes the
entire old original prefix [0,b), then selects one common finite
future f(W). A recursive diary may already have committed actual
parameters/gaps up to some later original cutoff F>=b. We must
realize all future clique profiles *beyond that cutoff*, keeping
the genuine original table E and all previously committed originals
fixed, without losing the old age.

A safe special case is to require that every newly selected future
original have **no ordinary-L edges to any original in [b,F)**.
This excludes a stage that intentionally joins a new reserved block
inside [b,F). It does, however, give a reusable arbitrary-delay
lemma for neutral insertion and for avoiding parameter/gap originals.

## Definition

Let c:Nat→Fin d→Bool be the complete typed old-column table and
0<=b<=F. Define its **neutral delayed extension**

```text
c^[b](p,t) = if p<b then c(p,t) else false.
```

The column is total, but at every p∈[b,F) it assigns zero for
*every* marked sort t. The original graph E on all old originals
remains completely unchanged.

For a genuine nonempty support T∈IntegerGraphSupport(d,ell), define
the complete common-neighbourhood pool

```text
R_b(T) = {p<b: for all t∈T, c(p,t)=true},
R_F(T) = {p<F: for all t∈T, c^[b](p,t)=true}.
```

## Lemma 1 — exact pool equality, no assumptions on E

For **every nonempty support T**, `R_F(T)=R_b(T)`.

*Forward.* If p∈R_F(T), choose any t0∈T (the support is
nonempty, so such a t0 genuinely exists). If p>=b,
`c^[b](p,t0)=false`, contradicting the required true bit.
Thus p<b and the membership conditions reduce to c on every t∈T.

*Reverse.* If p∈R_b(T), p<b<=F, and every c(p,t)=true
remains true in c^[b]. Hence p∈R_F(T).

The equality is literal equality of finite subsets of the SAME
old-original Nat enumeration, with no renaming or embedding. It
is independent of graph symmetry, loops, or clique-free hypotheses.

**Crucial adversarial check:** if T=∅, the condition
`∀t∈T` is vacuous and R_F(∅)=[0,F), while
R_b(∅)=[0,b). Equality is generally FALSE.
This is exactly why the proof uses a genuine
`IntegerGraphSupport d ell` with T.Nonempty,
not an arbitrary Finset support.

## Lemma 2 — exact raw AND canonical graph-age equality

Write

```text
B_b(T) = ell-1 - finiteDirectedCliqueCapacity(E,R_b(T)),
B_F(T) = ell-1 - finiteDirectedCliqueCapacity(E,R_F(T)).
```

Lemma 1 proves **pointwise** `B_F=B_b` at every
admissible nonempty support, for any E and ell (including
raw bound 0). Therefore

```text
integerGraphAgeCanonical(d,ell,B_F)
  = integerGraphAgeCanonical(d,ell,B_b)
```

by congruence. There is no illicit assertion B_b is
already a positive/genuine age; the equality holds for
arbitrary raw bounds, and the separately verified
singleton-safety theorem can be applied when needed.

Likewise the set of all feasible normalized integer clique
vectors is literally unchanged:
`feasibleIntegerCliqueVectors(d,ell,B_F)
 = feasibleIntegerCliqueVectors(d,ell,B_b)`.

This is stronger than only preserving a selected T-coordinate
or a list of independently witnessed maximizers.

## Theorem 3 — one uniform physical future beyond ANY prescribed F

Let E be the actual normalized Henson original graph, ell>=2,
d>=1, satisfying forbidden-family avoidance and
`OnePointLeftDense`. Let b<=F and any complete initial
typed old-column c.

Apply the kernel-checked
`henson_leftDense_realizes_all_finite_numericH_L_columns_and_profiles`
**at old prefix F**, prescribing the delayed column c^[b].
This theorem builds an explicit finite tagged universal
K_ell-free target over the ENTIRE literal [0,F) and embeds
it ONCE in the unchanged E. It yields one f, one finite
numeric-H carrier M and one common future pool W' after F.

The new uniform future has:

1. f(i)=i for EVERY i<F, not merely i<b;
2. every named fresh future original f(w)>=F;
3. for EVERY i<b and q<=k, both numerical-H ordinary-L
   directions from iota(i,q) to selected top iota(f(w),k)
   equal c(i,tau(w)), including zero bits;
4. for EVERY p∈[b,F), EVERY selected w and q<=k,
   both corresponding numerical-H L bits are **false**;
5. all genuinely skipped originals after F and before
   a later selected f(w) have zero L bits to that top
   at EVERY generation q<=k; odd dummy L bits also vanish;
6. the entire finite numeric-H top pool has **exactly**
   the normalized labelled-clique vectors feasible under
   the ORIGINAL age B_b, not some changed B_F;
7. all old-real and selected-top numeric coordinates tested
   are inside the same actual finite carrier M.

**One f, one M** provide every clause. The proof does not
concatenate independent existential choices: it invokes
the already checked common-witness theorem once at F
and rewrites the raw-bound function by Lemma 2.

## Hostile checks / limits

1. **Nonempty T necessary.** Empty-support common neighbours
   would include all newly padded originals; age equality fails.
2. **Zero bits on ALL padding originals.** Merely having a safe
   *selected* shadow inside [b,F) does not preserve the age.
   The whole interval must receive zero crossing columns.
3. **No hiding positive reserved-block edges.** A diary event
   whose new selected original must be adjacent to a newly
   reserved clique in [b,F) is not covered by this neutral
   padding lemma. Such events require Track B's mixed-support
   budget and revised reference-age invariant.
4. **Actual earlier E edges unchanged.** The padding
   originals may form arbitrary edges AMONG THEMSELVES
   and to [0,b); only their new-future crossing bits
   are forced zero. The full old prefix [0,F) is
   K_ell-free because E is Henson.
5. **Both directed L columns.** The symmetric original E
   and verified numeric-H top gate yield both orientations.
6. **No new original table.** f fixes every i<F
   pointwise. Nothing re-enumerates the fixed countable E.
7. **Arbitrary F≥b.** The future can be delayed beyond
   any previously fixed original cutoff, without
   choosing a separate future for each labelled vector.
8. **Canonical equality is pointwise on all supports.**
   It does not assert equality of two arbitrary old graphs;
   it uses the literal equality of common neighbourhood pools.
9. **Raw bound 0 is legitimate.** The future may omit an
   unsafe sort; do not conjure a forbidden one-point extension.
10. **Numeric carrier M is explicit.** It contains all real
    generations of [0,F), selected future top copies, and
    earlier skipped originals, as in the checked theorem.
11. **Auxiliary H+ E not covered.** Odd dummy ordinary L
    zeros do not imply their auxiliary parameter incidences vanish.
12. **No infinite resolved schedule.** Every invocation is
    finite and may choose a fresh f depending on F and c.
    Coherence of repeated calls through the canonical diary
    remains Track B's obligation.
13. **No source orbit or BRD claim.** This helps to
    schedule finite neutral stages, but does not prove
    parameter-closed B3, full labelled inverse source,
    occurrence factorization, or exact big Ramsey degrees.
14. **d=0:** the generic raw age equality is vacuous over
    admissible nonempty supports; the genuine uniform
    physical target theorem requires d>0 because its
    original input includes a total Nat→Fin d sort.
15. **ell=2 and k=0:** capacity is still calculated on
    nonempty supports, and top generation 0 is allowed.
16. **No fake age monotonicity:** B_F=B_b is equality,
    not an appeal to generic age monotonicity which would
    generally be in the opposite direction when extra
    positive old neighbours are introduced.

## Lean deliverables and acceptance

Create `Kk/CofinalNeutralOldColumnAge.lean` with:
- `delayedOldColumn` (the exact total Boolean table);
- `delayedOldCommonNeighbourPool_eq`;
- `delayedOldRawBound_eq`;
- `delayedOldCanonicalAge_eq`;
- `delayedOldFeasibleVectors_eq`;
- `henson_leftDense_uniform_numericH_after_neutral_delay`,
  an explicitly single-witness corollary with old/padding
  columns, no spurious labelled profiles, and M carrier bounds.

Strict exact-head `lake build Kk.CofinalNeutralOldColumnAge`,
fully qualified named transitive-axiom reports with only
`propext`, `Classical.choice`, `Quot.sound`, and
full `lake build` before any validation claims.
Keep central `Kk.lean`, `scripts/check_axioms.lean`,
`docs/validation.md`, `kk.tex`, `validation.tex`,
and protected black manuscript untouched.
