# Track A — ordered (nonconsecutive) numerical-H reserved-prefix capacity

**13 November 2026. English proof and adversarial audit before Lean.**

## Motivation and exact statement

The existing `finiteNumericH_reserved_block_prefix_capacity` assumes
reserved originals `N,N+1,...,N+r-1`. A fixed left-dense enumeration
will generally choose originals with gaps `q(0)<...<q(r-1)`.
The numerical-H real-copy gate depends only on the *order* of distinct
originals and their generations, not the differences between indices.
This gives the following required generalization without reindexing
the ambient original graph or silently treating gaps as non-existent.

For height `k`, a function `q:Nat→Nat`, pivot `0≤a<r≤k+1`,
generation `g≤k`, and original graph `E`, assume:

* `q(b)<q(c)` whenever `b<c<r` (only the finite block range is constrained);
* every `E(q(b),q(c))=true` for `b<c<r` and E is symmetric.

Let `Q_{q;a,g}` contain the literal numerical-H real coordinates
`iota_k(q(b),t)` for all `b<a,t≤k`, together with
`iota_k(q(a),t)` for `t≤g`. Here
`iota_k(i,t)=2(k+1)i+2t`. The exact **ordinary graph L** capacity is

```text
finiteDirectedCliqueCapacity (finiteNumericHL E k M).binary Q_{q;a,g}
    = if g<a then a else a+1.
```

This equality concerns the literal finite numerical-H *binary table*;
for physical carrier membership additionally assume
`iota_k(q(a),g)<M`. The finite model `M` does not affect the
binary table equality, but its carrier is necessary when interpreting
the result as a genuine finite structure.

## Proof

The image map `(b,t)↦iota_k(q(b),t)` is injective on the abstract
reserved-prefix pool: equality of bounded-generation positions implies
equality of original indices and generations by
`hPosition_injective_bounded`; finite strict monotonicity of q then
forces equal b. This explicitly excludes the aliasing
`iota(i,k+1)=iota(i+1,0)`.

For two different pool coordinates, there are three cases.

1. `b<c`: original clique and strict order give the exact literal
   numerical-H edge iff `t<u` or `t=u=k`, by the existing
   `hNumericBinary_real_forward_iff`.
2. `c<b`: reverse the endpoints, apply original symmetry and
   `hNumericBinary_symmetric_of_base`, and obtain the same edge gate
   in the reversed order. Both directed atoms are covered.
3. `b=c`: there is no numerical-H binary edge between two
   generations of a single original, using the already verified
   `hNumericBinary_same_original_false`.

Hence all off-diagonal pairwise binary atoms agree exactly with
`reservedCopyEdge k`, including negative bits. Use the existing
`reservedImageCliqueCapacity_eq_of_gate` and identification of
image clique capacity with `finiteDirectedCliqueCapacity`.
The generic abstract prefix theorem supplies the displayed formula.
This proof does not posit consecutive original indices.

For carrier membership: if `b=a`, then `t≤g` and the explicit
numerical formula makes its coordinate no larger than the pivot;
if `b<a`, the strict q-order and
`hPosition_lt_of_block_lt` put every generation up to k before
the pivot. Thus the whole prefix is inside the literal
`finiteNumericHL` carrier once the pivot position is below M.

## Hostile checks / statements explicitly NOT obtained

* **Gaps inside q:** unused original vertices between consecutive
  q-values are not in this Q; a full-prefix theorem must put all
  their numerical copies (and dummy coordinates) in G or another
  explicit pool, and prove their full zero crossing columns to W.
  The capacity computation alone does not assert such zeros.
* **No fake relabelling:** prove edges at original q(b) in the
  *unchanged* E; reindexing q abstractly and plugging N+b into
  E would be a different, unjustified model.
* **Strict order is necessary:** if q(b)=q(c), different reserved
  slots can represent different copies of one original, whose
  cross edges vanish even if the abstract block gate expects a clique.
* **Height is necessary:** without `a≤k`, the top-tie at g=k<a
  violates the lower-capacity branch.
* **Both orientations:** original symmetry matters to the directed
  clique test; positive forward arcs alone do not certify a clique.
* **Carrier:** `M` may be too small for the requested copies;
  only a separate numerical bound allows a physical interpretation.
* **Mixed cliques:** arbitrary older and gap coordinates can create
  extra cliques. The capacity of Q alone does not certify the
  relative marked-front condition; apply the *conditional*
  `finite_marked_front_gluing_iff_reference` only after proving
  all its old/reserve/gap/full-front hypotheses.
* **Not a global result:** this says nothing about the existence of
  a compatible infinite original schedule (Track B), auxiliary H+
  source data (C), B3 (D), or the common labelled orbit (E).

This is ordinary L only; E as the original adjacency table is **not**
the auxiliary Kpt E incidence.

## Lean acceptance

New independent module `Kk/NonconsecutiveReservedPrefix.lean`:
exact position injection, literal every-arc gate, exact capacity,
numeric carrier inclusion, and specialization of the complete
marked-front gluing criterion. Demand explicit module build,
fully-qualified strict standard-only transitive axiom reports,
and full `lake build` at the exact PR head. Manuscript marking
belongs to Track G.
