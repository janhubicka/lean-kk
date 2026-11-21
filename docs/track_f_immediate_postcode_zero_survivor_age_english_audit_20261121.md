# Track F — immediate post-code survivor age cannot jump at the zero bit

21 November 2026. **English proof and adversarial audit FIRST.** This is the next local ingredient after verified K4 actual code selection (#424), survivor synchronization (#433), and the two whole-age bridges (#436/#438). The entire cover/split/code history realization remains pending.

## Actual statement

Fix any ell, a true target ordinary graph E, and a finite family of GENUINE target Henson one-types `t_i`, indexed by Fin(d), each of level at least `c+1`. Suppose **every target type has bit zero at the selected original cut c**:

`c ∉ N(t_i)` for all i.

Let `p_i=restrictPrefix(t_i,c)` be the actual surviving type front immediately **before** reading the coordinate c, and `q_i=restrictPrefix(t_i,c+1)` the front immediately after reading it. By exact prefix restriction both are genuine safe Henson types. Since no t_i has c positive, the literal positive-neighbour sets are IDENTICAL:

`N(p_i) = N(q_i)`, since the only extra available coordinate from c to c+1 was c itself and it has bit zero.

For EVERY nonempty admissible sort support S, the common old-neighbour pools computed at c and c+1 agree literally. Indeed all entries of N(p_i) lie strictly below c, so even increasing the prefix from [0,c) to [0,c+1) adds no common neighbour to nonempty S. Thus all true RAW support bounds agree, and applying the normalized canonicalizer proves **equality of the complete canonical integer graph-age functions** of p and q (including every mixed triple support).

In the intended independent-code application c=e(r), merged PR #433 guarantees `c∉N(t_i)` for every surviving target t_i. This proves that the code's one target coordinate adds NO new ordinary-L canonical age restriction on the survivors, regardless of any other target branch order. It is an immediate **post-code survivor zero-bit** theorem, not the full pre-code age/split/history assertion.

## Proof details

- **Zero cutoff before/after:** For genuine t, the verified `restrictPrefix t L` has neighbour set `N(t)∩[0,L)`. If c∉N(t), then `N(t)∩[0,c)=N(t)∩[0,c+1)` by elementary Nat arithmetic.
- **Common pool equality:** For a nonempty support S, select one label i∈S. If x lies in the common pool at c+1, it lies in N(p_i) and therefore x<c; hence it lies in the pool at c. Reverse inclusion is immediate. The empty support is DELIBERATELY excluded because its pool is the entire old prefix and grows at every cut.
- **Raw equality:** Same graph E, same common pool ⇒ same finite directed clique capacity ⇒ exactly equal true RAW bounds `ell−1−cap` for each admissible nonempty S.
- **Canonical equality:** Equality of the complete raw support functions implies equality of their canonicalizations by pure function congruence; we neither require the raw tables themselves to be ages nor assume numerical raw=canonical equality.

## Hostile audit

1. Must have **c+1≤t_i.level** to take both genuine restrictions; a target type merely extending to c does not have a bit at c.
2. The target zero condition must hold **for EVERY surviving sort**; one survivor with bit 1 could change a mixed support or its singleton rank.
3. The negative bit is read from the genuine t_i target prefix, not inferred from source zero without actual coding witnesses; merged #433 supplies this hypothesis via true sourceCodingFibre.
4. A simple equality of positive sets suffices here because restrictPrefix is an actual type constructor retaining both positive and negative bits.
5. For nonempty S, a point in the later common pool belongs to an individual N(p_i), hence is below c. The empty-support pool does not obey the equality; it has no graph-age coordinate.
6. The proof uses true directed clique **capacity**, not raw common-neighbour cardinality.
7. All admissible support sizes are covered; equality is NOT just singleton/pair projection. Triple supports matter.
8. d=0 is vacuous; no Fin(0) element is chosen without a nonempty support witness.
9. ell=2 is allowed; there are only singleton supports, but the argument remains exact.
10. The canonicalizer can modify redundant bounds, but equal complete RAW functions yield equal canonical ages without any positivity or witness assumption.
11. The conclusion does not require source/target order-preserving embeddings or even an e; application to c=e(r) is separate.
12. This proves equality **immediately before/after reading the code coordinate on surviving types**. It does not assert the precode profile including the coded branch is F or that the selected coding branch was distinct from survivors.
13. The record code event also needs to verify the coded terminal's actual target type at level c and the canonical precode profile sandwich (#430/#438).
14. The statement does not exclude unrelated earlier or later hidden age events unless endpoint equalities and monotonicity are additionally supplied.
15. No frozen black manuscript text is changed, no global history or BRD lower marker promoted.

## Lean acceptance

Formalize (a) exact genuine prefix restriction equality at levels c and c+1 under a zero bit at c, (b) no-growth of actual common-neighbour pools under increasing cutoff with every old neighbour <c and NONEMPTY support, (c) raw equality on all admissible supports, (d) complete canonical integer-age equality. Dedicated exact-head Lean build and strict standard-only axiom reports; preserve manuscript history pending mark.
