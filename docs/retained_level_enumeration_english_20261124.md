# Actual level maps enumerate the retained slots

24 November 2026. English addendum before implementation of
`Kk/RetainedLevelEnumeration.lean`.

This gives the precise order argument used in Section 4 of
`retained_prefix_source_and_plan_seeds_english_20261124.md`. It removes
an independently assumed source size and independently assumed
coordinate-map identity once the actual level range is known.

## 1. Finite ordered ranges determine both length and enumeration

Let `f : Fin n -> Nat` and `g : Fin m -> Nat` be strictly increasing.
If their literal ranges are equal, then `n=m`. Both functions are
injective, so each finite range has the cardinality of its domain.
After transporting one domain along that equality, the two increasing
enumerations of the same finite ordered set coincide pointwise.

The uniqueness step is the usual rigidity of finite linear orders.
The library has this as
`StrictMono.range_inj_of_wellFoundedLT`; the finite cardinality equality
can be read from `Set.ncard_range_of_injective`. Neither an enumeration
identity nor an equality of source codes is an input.

## 2. Exact range through a represented cap endpoint

Take the following data:

- a strictly increasing actual numerical level function
  `lambda : Nat -> Nat`;
- a represented endpoint `lambda(n)=tau`;
- a strictly increasing list of ordinary retained positions
  `c : Fin M -> Nat`;
- the strict endpoint bounds `c(i)<tau` for every `i`;
- exact range through the endpoint:

      for every q<=tau,
      q in range(lambda) iff q in range(c) or q=tau.

Then

    n=M,
    lambda(i)=c(i) for every i:Fin M,
    lambda(M)=tau.

To prove this, append `tau` to the retained list. More explicitly define
`s : Fin (M+1) -> Nat` by `s(i)=c(i)` for `i<M` and `s(M)=tau`.
The strict endpoint bounds make `s` strictly increasing, with range
`range(c) union {tau}`.

The restriction `t : Fin (n+1) -> Nat`, `t(i)=lambda(i)`, is strictly
increasing. Its range is exactly `range(lambda) intersect {q:q<=tau}`:
the forward direction uses monotonicity and `lambda(n)=tau`; in the
reverse direction, a value `lambda(j)<=lambda(n)` forces `j<=n` by
strict monotonicity. Thus the stated exact-range premise gives
`range(t)=range(s)`.

Section 1 now gives `n+1=M+1`, hence `n=M`, and equality of the two
enumerations. Restricting to the first `M` indices yields the stated
literal coordinates. The endpoint is counted in both finite ranges
for this argument, and then excluded from the ordinary coordinates.

## 3. Actual Kpt shape-map version

Let `F` be an actual Kpt shape map, with an actual source cap `U*` and
target cap `U` satisfying `F(U*)=U`. Put `tau=lev(U)` and
`lambda=kptShapeLevelMap family F`. Suppose the strictly increasing
positions `c : Fin M -> Nat` satisfy `c(i)<tau`, and

    F.levelRange =
      {q : q in range(c) or q=tau or tau<q}.

The already proved `kptShapeLevelMap_strictMono`,
`kptShapeLevelMap_eq`, and `kptShapeLevelMap_range` supply respectively
strictness, `lambda(lev(U*))=tau`, and the numerical range identity.
Section 2 therefore derives

    lev(U*)=M,
    kptShapeLevelMap family F (i.val)=c(i) for every i:Fin M.

The exact level-range hypothesis is available from
`plannedPrefixSeeds_run_exact_plan` once the explicit Plan has been
identified with the slot range plus the cap endpoint. The shape-map
version does not assume `lev(U*)=M`, preimage-table equality, or that
its level map already agrees with the retained coordinates.

## 4. Literal ordinary-code recovery with those coordinates

For each slot put `rho(i)=<c(i), c(i)<tau> : Fin tau`.
The actual source cap has the complete ordinary code

    ordinaryCode(U*) = ordinaryCode(U).reindex M rho.

Indeed `shapeMap_recovers_ordinaryCode` first recovers it along
`retainedSocleIndex family F U*`, whose values are the actual numerical
level map. Section 3 supplies its length and every value. Transport
along the derived length equality, using the existing
`FinitePartialCode.reindex_change_size`, changes the index domain to
`Fin M`. Extensionality of finite indices identifies that map with
`rho`. This is equality of all four finite tables, including absent
ordinary and directed E atoms, and not a raw distinguished-type
identity.

Combining this conclusion with `RetainedChunkTables` leaves only the
construction-specific tasks of extracting the same ordered slot data
from equal records and identifying the actual Plan as that slot range
plus endpoint. No separate source-size or retained-map premise remains
in this bridge.

## 5. Boundary checks

The finite ordered-range statement allows `n=0` or `m=0`. The endpoint
statement allows `M=0`; then it derives `n=0` and contains no ordinary
coordinate assertion. It does not claim a positive-size G+ vertex.

If `tau=0`, the strict bounds `c(i)<tau` force `M=0`, and therefore
`n=0`. In particular the anchor cannot simultaneously be counted as
an ordinary slot and as the endpoint zero. This handles the degenerate
cap honestly. The manuscript's `n>=1` selected-terminal construction
has a positive slot strictly before the cap and hence a positive
source ordinary code.

The proof does not require `lambda(0)=0`. The actual application has
the retained anchor in its slot list when the cap is positive, but the
generic ordered-range argument makes no unnecessary root assumption.
Repeated physical occurrences of the same ordered record may have
different numerical slots and different maps; each map is identified
with its own literal ordered slot list, and the chunk-table theorem
then compares their codes using the common tags.
