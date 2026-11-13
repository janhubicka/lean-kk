# Track A — when the finite old-column canonicalizer is a genuine positive graph age

**13 November 2026. English proof and hostile audit BEFORE Lean.**
This is a small independent strengthening of the finite reference-age
bridge in Track A PR #113; it does not change existing proof files or
any manuscript validation markers.

## Definitions / exact input

Let ell>=2, d>=0, E:Nat→Nat→Bool be an arbitrary directed Boolean
ordinary graph-L table, P a finite old pool, and
c:Nat→Fin d→Bool the entire specified old-to-labelled-future bit
column function. The finite reference-age raw bound from PR #113 is

    B_P(T) = ell - 1 - cap_E(R_P(T)),
    R_P(T) = {p∈P : ∀t∈T, c(p,t)=true}.

The only old-neighbourhood certificate needed for positivity is

    for every t:Fin d,
      cap_E({p∈P : c(p,t)=true}) < ell - 1.

This is the precise finite-clique form of every marked singleton
type being eligible for a one-point extension: there is no
(ell-1)-clique in its complete old neighbourhood. If the actual
old graph is K_ell-free, and each prescribed type is symmetric in
both crossing orientations, the original Henson one-point
criterion then realizes that individual type over P. We do NOT
assume simultaneous realization of all types or their mutual edges.

## Lemma 1: a genuine constant-one integer graph age

For ell>=2, define H(U)=1 for every admissible nonempty
U∈IntegerGraphSupport(d,ell). Then H is an
IsIntegerGraphAge d ell.

Proof: each value lies in [1,ell-1]. To witness H(U)=1,
choose t∈U and the normalized integer weight vector with
exactly one vertex of sort t and zero vertices of all other sorts.
Every supported count is 0 or 1, hence ≤H(V) for each V; the
U-count is exactly 1. The witness is normalized, total size 1≤ell-1.
For d=0, no nonempty supports exist, so the consistency condition
is vacuous. There is no choice of a nonexistent sort.

## Lemma 2: singleton safety implies positivity of EVERY raw support

Fix U∈IntegerGraphSupport(d,ell). Choose any t∈U.
Every vertex p adjacent to all sorts in U is in particular
adjacent to t, so

    R_P(U) ⊆ {p∈P:c(p,t)=true}.

Monotonicity of the *actual directed clique capacity* gives

    cap_E(R_P(U)) ≤ cap_E({p:c(p,t)=true}) < ell-1.

Because ell≥2, this yields
    1 ≤ ell-1 - cap_E(R_P(U)) = B_P(U).

This is the missing condition that rules out zero raw bounds,
without fabricating a global geometric realization.

## Lemma 3: canonicalized old-column age is genuinely admissible

Let H be the constant-one graph age. Lemma 2 gives
H≤B_P on EVERY nonempty admissible support. Apply the already
proved `integerGraphAgeCanonical_is_age` with H to obtain

    IsIntegerGraphAge d ell (integerGraphAgeCanonical d ell B_P).

This derives, rather than assumes, both the positivity and all
integer-witness consistency axioms of the physical reference age.
Together with PR #113, the resulting canonical age controls
the **entire** joint labelled finite continuation profile.

The result remains conditional on each original marked singleton
column being safe. Such singleton certificates may be supplied
by Track B's mixed-neighbourhood recursion; this lemma does not
supply the actual unbounded selection schedule.

## Hostile boundary checks

1. Without the singleton certificate, positivity can fail.
   Example ell=3, old edge p--q and a future sort t whose
   prescribed column sees both p,q. Then cap(R({t}))=2,
   B({t})=0: no singleton t can be added without a triangle.
2. Ell=1 is excluded. The genuine age requires F(U)≥1 but
   ell-1=0; the integer support family may be empty.
3. Empty d is allowed: no admissible T exists; both singleton
   safety and consistency are vacuous. Do not construct an
   artificial element of Fin 0.
4. Old neighbourhood *cardinality* is irrelevant; use clique
   capacity. Several independent neighbours of t are safe
   even when their set is large.
5. The chosen t may depend on support U; the bound nevertheless
   holds simultaneously for **all** supports by universal
   quantification of singleton safety.
6. The raw function B_P need not itself satisfy integer-age
   consistency. We prove it lies above a genuine age, so its
   **canonicalization** is a genuine age.
7. The result is about ordinary graph L and integer clique
   profiles. It says nothing about auxiliary Kpt E, corrected
   B3, or common labelled inverse-source orbits.
8. The singletons may individually be realizable, yet an arbitrary
   family of future originals with prescribed internal edges can
   violate K_ell. Whole-front relative realizability still
   requires the *full glued graph* safe.
9. The physical old E may contain parameters and gaps; singleton
   safety must test the COMPLETE old original neighbourhood,
   not merely its selected shadow.
10. The existing exact reference age and the new positive-age
    property do NOT by themselves prove the recursive invariant
    that the old reference age equals a particular intended
    upper graph age at every diary stage.

## Lean plan and audit

Add `Kk/FiniteOldColumnAgePositive.lean` importing
`Kk.FiniteOldColumnAge` and the checked finite integer clique
weight constructor. Prove:
- `integerGraphAge_const_one_is_age`;
- `finiteOldColumnRawBound_positive_of_singleton_safe`;
- `finiteOldColumnCanonical_is_age_of_singleton_safe`.
No sorry, admit or new axioms. Explicit exact-head module build,
fully qualified named strict transitive-axiom report, and complete
`lake build` before any validation promotion. Integration owner
Track G controls the central Lean aggregator and manuscript marks.
