# Track A — pinned-prefix chronological finite Henson realization

**13 November 2026. English proof with hostile checks, preceding new Lean code.**

## Statement

Let `A,E : Nat → Nat → Bool`, integers `b≤N`, and `ell>0`.
Assume:

1. A is symmetric and irreflexive, and `A|_[0,N)` is `K_ell`-free.
2. Every finite prefix of E is `K_ell`-free, and E satisfies the
   actual manuscript `OnePointLeftDense E ell` property.
3. **Complete old agreement:** on every ordered off-diagonal pair
   `i,j<b`, `A(i,j)=E(i,j)`. In particular the fixed prefix is
   the **entire physical enumeration** `[0,b)`, not just selected
   old vertices.

Then there is a strictly increasing induced embedding
`f:[0,N)→Nat` into the same E such that `f(i)=i` for every
`i<b`, every ordered edge among images equals A, and for each newly
embedded original `n∈[b,N)`:

```text
z<f(n) and z ∉ f([0,n))
  implies E(z,f(n))=E(f(n),z)=false.
```

There is NO claim that `f(n)=n` for new n, nor that a separate
arbitrary abstract finite clique is realizable over an incompatible
old column. The statement is about complete ordinary graph L.

## Induction proof

Prove simultaneously the four conclusions for each initial target
segment `[0,n)`, `0≤n≤N`.

If `n≤b`, use the identity function. This is an induced graph map
because of the *complete old agreement*; the gap conclusion has no
indices `m` with `b≤m<n`.

For a successor stage `n≥b`, let P be the first n abstract indices.
By induction choose f for P, pinned on the old b coordinates, strictly
increasing, and inducing A exactly. Let

```text
S = {i<n : A(i,n)=true}.
```

Because A on `[0,n+1)` is K_ell-free, S has no directed
`K_(ell-1)`. Otherwise S together with n would form a forbidden
clique, using A's symmetry and irreflexivity. The existing theorem
`hasCliqueBelow_succ_iff_old_or_neighbour` and finite checker give
this *complete* negative old-neighbourhood certificate, not merely
one reserved-block cardinal estimate.

The already constructed f is injective on P and preserves every
ordered off-diagonal L edge. Thus
`finitePoolCliqueCheck_false_iff_induced_image` transfers the
certificate to the genuinely embedded neighbour set `f(S)`.
Choose a front strictly above f(P). E is K_ell-free below this
front, so `onePointLeftDense_extend_finite_induced_copy` supplies a
genuine later original v with exact A columns to every old f(i),
in BOTH directions, and all intervening vertices not in f(P)
nonadjacent to v. Extend the embedding by f(n)=v, leaving every
previous f(i) unchanged. This preserves the pinned prefix, strict
order, all directed induced edges and the zero-gap assertion.

For an earlier m<n the final embedding f' agrees with f on every
index below m; therefore the image set `f'([0,m))` equals
`f([0,m))`, and the previous zero-gap assertions remain true.
For the new n, the one-point extension theorem supplies the zeros.
This closes induction.

For the normalized Henson graph, the existing
`hensonForbiddenFamily_no_prefix_cliques` supplies the hypothesis
of prefix K-free E from actual forbidden-family avoidance. The
fixed enumeration's `OnePointLeftDense` remains explicitly assumed.

## Adversarial audit

1. **Must require full glued A K-free.** With ell=3, old p and future
   q,r adjacent to p, the abstract edge q–r alone is triangle-free,
   but the prescribed glued extension pqr is not. The theorem rejects
   this case because its K-free A hypothesis fails.
2. **Not just positive columns:** the induced-copy theorem has ALL
   A(i,n) bits, including prescribed absent neighbours, and both
   ordered L arcs. A positive-neighbourhood-only embedding would not
   prove the claimed relative age.
3. **Entire fixed prefix, not selected subpool:** if one pins only
   selected old vertices and leaves gaps outside the base, the
   injection may not fix the original chronological segment. We
   demand agreement on all distinct `i,j<b` and `f(i)=i` for
   every i<b.
4. **Intervening gaps:** the zero assertion concerns every
   `z<f(n)` not an earlier image, not just gaps after the last
   reserved vertex. It is provided by left density at each stage,
   and retained under later extensions.
5. **Boundary b=N:** the identity embedding is a witness; there are
   no newly embedded originals. This cannot be confused with an
   unbounded stage schedule.
6. **Boundary b=0:** start from the empty pinned prefix; the first
   extension is a valid one-point left-dense step with an empty
   neighbour set when the finite A is safe.
7. **Multiplicity of sorts:** this theorem embeds every *finite
   graph pattern* A one at a time. Different new vertices can later
   receive the same marked sort and identical columns to [0,b),
   but a *single* fixed set of top names need not realize every
   abstract W simultaneously as induced edges.
8. **No hidden completion axiom:** avoidance of the normalized Henson
   forbidden family and the explicit `OnePointLeftDense` are the
   only global ambient assumptions used. Extension of a finite
   compatible pattern is a consequence, not an additional axiom.
9. **No numerical or H+ conclusion:** to get the literal numerical-H
   prefix L profiles, transport the new originals through hPosition
   and prove the correct ordered real-copy gate, every dummy/gap
   column, and future top copies. The auxiliary Kpt E and
   parameter-closed B3 are outside Track A.

## Formalization / audit rule

Implement in a separate `Kk/PinnedPrefixHensonExtension.lean` from
the existing one-point induced extension and clique-check transport.
Include the global zero-to-intervening-indices output as an explicit
third component. Add fully qualified `#print axioms` for all public
endpoints; compile explicitly, check standard-only transitive axioms,
then the full library at the exact feature-branch head. No manuscript
green marks before integration and geometry closure.
