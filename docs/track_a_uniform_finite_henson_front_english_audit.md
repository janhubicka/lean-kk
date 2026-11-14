# Track A — simultaneous finite labelled-clique profiles over one fixed Henson prefix

**14 November 2026. English proof and adversarial audit BEFORE Lean.**

This work starts on the currently integrated `lean-kk/main` after PR #126.
It isolates the quantifier issue left open by the finite physical-age
calculation: `forall feasible w, exists a compatible finite occurrence`
does NOT immediately yield `exists ONE fixed finite Henson extension,
forall feasible w, some occurrence is inside it`. The result below
carries out the simultaneous transport of any **single finite universal
target** with a full old-prefix compatibility certificate. Existence
of that target over the prescribed old prefix remains an independent
finite gluing/construction obligation, not an axiom.

## Exact theorem

Let E be the actual infinite symmetric loop-free Henson original
graph with `OnePointLeftDense E ell` and avoidance of the
normalized forbidden family, ell>=2. Fix the *entire consecutive
old original prefix* [0,b), N>=b, and a finite target ordinary-L
graph A on [0,N), symmetric, loop-free, K_ell-free and **agreeing
on every old pair** with the fixed E on [0,b). Let W be any
finite subset of [b,N), carrying a sort map `tau:Nat→Fin d`.
Let B be an arbitrary raw support bound.

Suppose the SAME target W has this exact universal finite
labelled-clique profile:

  (1) for every feasible normalized integer clique vector v
      (respecting B on ALL supports), there exists a directed
      A-clique s⊆W with ALL support-count multiplicities exactly v;
  (2) every directed A-clique s⊆W respects ALL B support bounds.

The checked pinned-prefix theorem supplies ONE monotone embedding
f:[0,N)→Nat of A into the **unchanged fixed E**, with
f(i)=i for every i<b, exact ordered *positive and negative*
L atoms, and chronological zero-to-skipped-original columns
for every new vertex.

Define the physical future pool `W'=f(W)`. Instead of guessing
a global sort labelling on all of Nat (which is impossible if d=0),
use the intrinsic **pulled-back sort predicate** on W':

  `IsSortIn_T(z) :↔ ∃x∈W, f(x)=z ∧ tau(x)∈T`.

Then with the SAME single f and W' all feasible vectors v
have actual E-clique witnesses s'⊆W' whose IsSortIn_T
cardinalities equal v(T) simultaneously for EVERY support T;
and EVERY E-clique s'⊆W' obeys the original B support bounds.

This is stronger than independently embedding one clique per vector:
the witnesses coexist in ONE finite physical future W', in one
fixed original enumeration over the identity old prefix.

## Proof in English

The pinned-prefix theorem provides one f for the whole finite A,
not a separate f for each normalized vector. It is strictly
increasing on the entire target range [0,N), hence injective
on W. For a finite A-clique s⊆W define s':=f(s). Exact
off-diagonal old/future/future atoms imply s' is an E-clique
in f(W). Injectivity and the pulled-back typing predicate give
for every T the finite-set identity

  `f(s) ∩ IsSortIn_T = f(s ∩ tau^{-1}(T))`.

The cardinality identity follows by finite-image injectivity.
Therefore all witness multiplicities are preserved *together*.
The chosen finite target clique may depend on v, but the ambient
f and W' DO NOT depend on v. This closes the quantifier swap.

For the absence of spurious clique vectors, take an arbitrary
E-clique t⊆f(W). Its pullback
`s = {x∈W:f(x)∈t}` is an A-clique, and f(s)=t.
Both directed edge atoms transfer backwards via the exact
induced relation. The same filter/cardinality identity gives
the B constraints for t from those for s.

The pinned theorem also supplies the gap-zero assertion
for all new target vertices: every earlier ambient original not
already in f([0,m)) has zero edges to f(m), both directions.
In particular future witness copies are chronologically later
than every fixed old original and receive no accidental
links from omitted intervening originals.

## Hostile checks and boundaries

1. **The universal target A must exist.** It is not legitimate
   to take the standalone W_B from
   `UniversalFutureExactProfile` and assume it attaches
   over an arbitrary old prefix. The old graph must be glued
   to W_B with BOTH prescribed typed crossing columns,
   and its entire K_ell-freeness must be checked.
2. **One f, not one f_v.** The theorem applies pinned embedding
   exactly once to the *whole* A. Applying it separately for
   every v produces unrelated actual pasts and does not prove
   the simultaneous statement.
3. **Full old prefix.** The old identity domain must be all
   [0,b), not just a selected old subset; any old gaps within b
   can otherwise destroy relative adjacency compatibility.
4. **Future W after b.** No designated future index is before
   the pinned prefix; W⊆[b,N) is explicit.
5. **No sort map on Fin 0.** The pulled-back supported-sort
   predicate is meaningful for d=0, when there are no labelled
   vertices or nonempty admissible supports; a total
   `Nat→Fin 0` cannot exist. The theorem accepts a sort
   map parameter and therefore d=0 only when its input is
   itself inhabited; no fabricated sort is constructed.
6. **Negative directions.** The original pinned theorem gives
   all off-diagonal ordered L equalities, not only positive
   edges. Both forward and backward clique transport use them.
7. **No unsupported identification of f(W) with a numeric top pool.**
   One gets real original vertices at arbitrary, strictly
   increasing original indices. Their top-generation numeric
   copies can be formed using `hPosition` and the existing
   `numericH_older_generation_to_top_exact` only after the
   concrete generation/order conditions are verified.
8. **No promise that all abstract W configurations are induced.**
   The universal target captures every *feasible clique vector*
   (sufficient for integer graph-age profile). It does not
   contain every arbitrary labelled finite graph as an induced
   subgraph, nor certify full B3/auxiliary E sources.
9. **No global infinite construction.** The pinned theorem
   produces one finite compatible extension; it does not
   maintain the intended canonical upper age through
   infinitely many diary steps.
10. **Raw bounds need not be positive.** If some B(U)=0
    the feasible clique family simply omits corresponding
    profiles. The new theorem preserves exact feasible vectors
    without presuming B itself is a genuine graph age.
11. **Zero-to-gap quantifiers.** At stage m the zero assertion is
    only to z < f(m) outside the images of earlier target
    vertices. It does not imply all selected future vertices
    are pairwise nonadjacent; their A-clique internal edges are
    preserved as prescribed.
12. **Uniform witness set is finite.** The finite type of
    normalized integer clique vectors has finitely many
    members; the tagged disjoint-clique construction
    `UniversalFutureDisjointCliques` supplies a standalone
    W_B with exact finite profile. One must still glue this
    W_B to the actual fixed old graph using the *complete
    original* crossing columns and verify the mixed-clique
    condition before applying the present theorem.

## Next independent mathematical obligation

For any fixed old original prefix [0,b) and complete prescribed
old columns c, construct the finite **tagged free amalgam**
A of that old prefix with the existing universal future W_{B_P}
(B_P computed from common old-neighbour clique capacities).
Give distinct new Nat names to each tagged future vertex,
make edges within future components exactly those of
`universalWitnessEdge`, different components nonadjacent,
and old/new edges exactly c in both directions. Use the
already verified `finiteOldFuture_free_iff_raw_support`
plus `universalWitnessFuture_clique_respects_raw`
to prove the joined finite A is K_ell-free.
Then the present theorem produces an unconditional **finite**
universal front in the fixed Henson original graph for any
compatible old-column c, subject only to the true
old-prefix Kfree/Henson left density. This would close the
finite quantifier gap, while leaving the infinite resolved
schedule and auxiliary H+ obligations to B/C/D/E.

## Lean acceptance

Add `Kk/UniformFiniteHensonFront.lean` containing
a sharp finite-image support-count preservation lemma and
the one-embedding-all-witnesses result, plus an exact
normalized-Henson corollary. Fully qualified named
`#print axioms`, dedicated new module build,
strict standard-only transitive-axiom parser,
and full `lake build` at the exact PR head.
Do not touch the global aggregator/markers or black manuscript.
