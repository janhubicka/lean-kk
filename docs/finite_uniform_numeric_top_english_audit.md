# Track A — one genuine numerical-H top generation carries the entire finite Henson clique profile

**14 November 2026. English proof and adversarial audit BEFORE Lean.**

This is a separate follow-up to the exact-head-verified finite uniform original Henson result
[PR #157](https://github.com/janhubicka/lean-kk/pull/157).
Its own branch is stacked on #157 and imports the literal numerical-H constructors already
verified in main. No existing source, central axiom inventory, or manuscript is edited.

## Statement 1 — complete top-to-top ordinary-L identity

For any symmetric Boolean original graph E, height k, finite numerical carrier cutoff M, and
**distinct** original indices i,j, the literal finite numerical-H binary L bit satisfies

```
L^H_{k,M}(iota_k(i,k), iota_k(j,k)) = E(i,j)
```

including **false** bits, in both ordered orientations. For i<j, the verified theorem
`numericH_older_generation_to_top_exact` applies with earlier generation q=k: its top-to-top
gate is open by the exceptional equality q=k. For j<i, apply the exact numerical-H symmetry
theorem then the forward formula for j,i and the original symmetry. Distinctness matters:
the numerical model's self-bit is false independently of an arbitrary original loop E(i,i).

The top-position map i↦iota_k(i,k) is globally injective
(`numericHTopPos_injective`).

## Statement 2 — finite induced cliques and supported cardinalities

For every finite set s of original indices,

```
IsDirectedCliqueOn E s
 iff
IsDirectedCliqueOn L^H_{k,M} (numericHTopPool k s).
```

Use the existing exact finite-induced-image clique transport, with the global top-position
injection and **all off-diagonal ordered L atoms**, not just forward positives.

For all finite s,C⊆Nat,

```
|{z∈numericHTopPool k s : z∈numericHTopPool k C}|
  = |{i∈s : i∈C}|.
```

Prove set equality of the filtered image and the image of the filter; injectivity of
i↦iota_k(i,k) gives the cardinality. C need not be all of s, a clique, or an upward-closed
type pool.

## Statement 3 — uniform profile transport for one original future

Let S⊆Nat be ONE finite original future, and for each admissible support T let C(T)⊆Nat
be its finite supported-original pool. Suppose S has the complete exact raw age profile:

```
for EVERY normalized labelled weight v,
  v∈feasibleIntegerCliqueVectors(d,ell,B)
  iff
  some directed E-clique s⊆S has
    |s∩C(T)| = integerCliqueOnSupport(v,T)
  for ALL admissible T.
```

Then the SAME finite numerical-H top pool S_k=numericHTopPool(k,S) has the exact profile
with support T read as membership in numericHTopPool(k,C(T)).
The proof transports a witness by the top injection, and reverses the construction with the
finite preimage s={i∈S:iota_k(i,k)∈t} of an arbitrary top clique t⊆S_k.
The clique equivalence and supported-cardinality identity prove *both* directions.
No extra age-canonicity assertion, extra original vertex, or universal quantifier swap is
inserted.

## Statement 4 — a single genuine finite-H carrier and a physical Henson corollary

Let E be the unchanged normalized K_ell-free left-dense Henson original graph, ell≥2, d>0,
and fix its entire original prefix [0,b) and arbitrary complete typed old-to-future
columns c(p,t). The already checked Track A theorem
`henson_leftDense_realizes_all_finite_relative_age_profiles` produces ONE actual
original embedding f and ONE finite original future S=f(W) such that every raw-feasible
normalized vector is realized by an E-clique in S, with no spurious profiles. It also pins
the entire old prefix and makes every named new original nonadjacent to previously skipped
originals.

Choose a genuine numeric carrier cutoff, e.g.

```
M = 1 + sup { iota_k(j,k) : j∈([0,b) ∪ S) }.
```

This simultaneously places the top-generation images of **all old original vertices** and
every selected new original into the actual finite numerical-H carrier [0,M).
When S and b are empty, M=1 is legitimate.
The future top pool S_k=numericHTopPool k S and its supported top pools

```
C_k(T) = numericHTopPool k ((W.filter (tau∈T)).image f)
```

exist in the SAME finite numeric H L table. By Statements 1–3, the very same f (and selected
finite M) yields the exact feasible-integer-clique-vector iff in that top pool, simultaneously
for all vectors and all supports.

This is the genuine finite **ordinary-L numerical-H top generation** of one chosen uniform
future. It does not assert its (L^+) source type, all-parameter closure, B3, or
an infinite coherent chosen resolved schedule.

## Adversarial checks

1. **Top-to-top exceptional gate:** at equal generation k, the numerical-H edge gate is
   open only because both are at the TOP k, not for arbitrary equal lower generations.
2. **Distinct original labels:** the off-diagonal transport must exclude i=j; the underlying
   original E need not be loop-free for the generic bit identity.
3. **Two directed arcs:** the reverse identity requires symmetric original E, not just a
   positive increasing edge.
4. **False bits preserved:** an induced finite graph copy needs all nonedges, not just the
   labelled cliques that attain a maximum.
5. **Finite-carrier semantics:** Boolean L is defined on all Nat positions; explicitly
   choose M so every *tested top coordinate* lies in the true finite carrier. A total
   outside-carrier table alone is insufficient.
6. **Old prefix bounded too:** M is based on the union of old original indices and selected
   new originals, not just S; otherwise an empty S could leave the old physical top
   originals outside the finite carrier.
7. **No auxiliary Kpt E proof:** binary L agreement at top does not identify the full
   parameter-closed H+ source or corrected B3 events.
8. **No consecutive original names:** actual f(W) may be widely separated; the proof uses
   the original indices unchanged, not a re-enumerated Henson graph.
9. **All normalized vectors in one future:** the existential clique depends on the vector,
   but f, S, M, and S_k are independent of it.
10. **No new old adjacency:** f fixes every old original and controls the skipped originals
    through the pinned-prefix theorem; numeric top transport does not introduce additional
    original edges.
11. **No false default sort label:** each support T is a genuine finite image C_k(T);
    it does not attempt to colour all unrelated numeric-H coordinates with a Fin d value.
12. **No guarantee of stage invariants:** old/reserved block columns, numeric prefix
    isolation, and canonical cover-state preservation in the actual infinite selected
    diary are still separate from a finite uniform top future.
13. **No BRD conclusion:** finite ordinary-L universality alone does not establish
    bounded resolved copies, occurrence factorization, or diary unavoidability.
14. **Boundary k=0:** the top generation is 0 and the exceptional equal-top gate still
    applies for distinct originals. The carrier/copy argument remains valid.
15. **Boundary empty S/d=0:** empty S is allowed. The final Henson uniform theorem assumes
    d>0 to define total old-to-new typed columns; the generic top-image transfer can still
    be stated independently of any d>0 assumption.

## Lean plan

Create independent `Kk/FiniteUniformNumericTopAge.lean`:
- `finiteNumericH_top_exact_original_edge`
- `finiteNumericH_top_clique_iff_original`
- `finiteNumericH_top_supported_count_eq`
- `finiteNumericH_top_profile_iff_original`
- `finiteNumericH_top_carrier_of_sup_cut`
- `henson_leftDense_realizes_all_finite_numericTop_profiles`

First compile the exact top-bit and finite clique/cardinality lemmas, then the finite raw
profile transport and #157 specialization. Strict fully-qualified named `#print axioms`
reports, an explicit module build and a complete `lake build` at exact PR head are
required before calling any additional endpoint verified.

Review/integration remains with Track G. Do not touch Kk.lean, scripts/check_axioms.lean,
docs/validation.md, kk.tex, validation.tex, or black manuscript prose.
