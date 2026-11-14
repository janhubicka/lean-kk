# Track A — exact Nat numbering of a finite tagged future over a fixed old prefix

**14 November 2026. English argument and hostile audit BEFORE Lean.**

This is the first constructive step needed to replace the existential
compatible finite target assumption of PR #137. The standalone universal
future `universalWitnessFuture` is a finite dependent-sum type, whereas
the pinned-prefix Henson embedding theorem takes a symmetric loop-free
Boolean table on Nat with a **literal fixed old initial segment**
[0,b). Re-enumerating the old initial segment is forbidden: it must
remain the identity in the unchanged Henson original enumeration.

## Exact finite numbering

For any finite type V and any natural old-prefix length b, choose
one bijection `e: V ≃ Fin(card V)` (classically). Put

  code_b(v) = b + (e v).val.

The code is injective, and its image is *exactly* the interval
`{n : b≤n<b+card V}`. These facts hold even for V=empty;
no phantom future name is introduced.

Define `decode_b(n):Option V` to be `some(e.symm(n-b))`
when b≤n<b+card V, and `none` otherwise. The subtraction
and Fin index are justified by the same strict upper bound,
including the potentially empty interval. Then
`decode_b(code_b(v))=some v`. This is a **total** Option-valued
decoder and does not require a nonexistent default vertex of
an empty future type.

## Exact old-plus-future ordinary-L binary table

Given an actual old-original Boolean table E, a symmetric loop-free
finite future table R on V, a label map `tau:V→Fin d`, and
COMPLETE typed old-to-future columns `c:Nat→Fin d→Bool`,
define a **total Nat table** A_b by cases:

- both coordinates <b: `A_b(x,y)=E(x,y)`;
- old x<b, future y=code(v): `A_b(x,y)=c(x,tau(v))`;
- future x=code(v), old y<b: `A_b(x,y)=c(y,tau(v))`;
- future x=code(u), future y=code(v):
  `A_b(x,y)=R(u,v)`;
- outside both the old prefix and the correctly coded future
  interval: all other binary bits are false.

The above is a precise Boolean **definition**, not merely an
adjacency-preserving embedding claim. If E is symmetric and
loop-free on its old prefix and R is symmetric/irreflexive,
then the new total A_b is symmetric and irreflexive.
It agrees literally with E on the entire old prefix,
has exact two-direction typed columns, and carries the
whole future R table—including zero bits—in the correctly
numbered interval.

Define `sort_b(n)` by decoding when possible, defaulting to
an arbitrary element of `Fin d` outside the future. This
total sort map is used **only if d>0**; the Option decoder itself
works at d=0. On each valid future position,
`sort_b(code_b(v))=tau(v)` exactly.

## Adversarial checks

1. `card V=0`: there are no future codes, so never extract
   an element of V by global `Classical.choice`.
2. `b=0`: the entire initial segment is future, with
   no incorrectly assumed old neighbours.
3. The decoder is defined only on [b,b+card V), so
   coordinates beyond the target size are neutral and
   do not create off-diagonal relationships.
4. The original old graph's arbitrary vertices >=b
   are NOT copied into this target; those belong to the
   ambient physical E and will be skipped by left density.
5. In the old/future crossing cases, both directed atoms
   use *the same* typed column c. Positive-only copying
   would not produce an induced relative embedding.
6. The future/future case copies all R bits, including
   nonedges between different normalized witness components.
7. A_b is total and its loop-freeness outside the
   old+future range follows from the false fallback, not
   from a hidden ambient irreflexivity assertion.
8. A b-prefix value E(x,y) is reproduced ONLY when both
   indices are <b. Later physical original E bits are
   not illicitly treated as part of the requested target.
9. No numerical-H generation is inferred from this code.
   The new indices are *abstract requested original names*;
   the pinned Henson embedding sends them to actual
   later originals, and only then are their top-generation
   numerical-H copies constructed.
10. The numbering alone does NOT prove the glued graph
    K_ell-free. That requires the old-prefix free
    certificate plus the complete normalized raw
    support bounds of the future universal graph.
11. The source finite universal future may be a
    dependent subtype of a tagged Sigma type; finite
    bijection to a Fin index works without choosing a
    canonical order on the future type.
12. All typed mappings of valid coded future names
    are exact, but their values on **other** Nat indices
    are arbitrary. Do not infer a global labelled
    Henson expansion from the auxiliary default.

## Next composition

Instantiate V with the subtype of feasible vertices in
`UniversalWitnessFuture`, R with the checked
`universalWitnessEdge`, and raw bound
`B_P(T)=ell−1−cap_E({p<b:c(p,t)=1 for all t∈T})`.
The exact profile lemmas of `UniversalFutureExactProfile`
transport along code_b to the finite target future W_b.
Then `finiteOldFuture_free_of_all_raw_support` proves
the **whole glued target A_b** K_ell-free from the old
prefix K_ell-free condition and all future raw bounds.
Applying PR #137's single pinned embedding theorem will
yield a common actual finite physical future containing
simultaneous witnesses of ALL feasible labelled clique vectors.
This is the remaining finite existence bridge, not yet a
proved consequence of mere numbering.

## Lean acceptance

Add `Kk/FiniteTaggedFutureEncoding.lean` with exact
finite code/decode, interval equivalence, total old/future
binary table and symmetry/irreflexivity/exact columns,
and optional sort transfer for d>0.
Require explicit exact-head module build and named strict
standard-only axiom reports, followed by full `lake build`.
No global validation marks or frozen manuscript edits.
