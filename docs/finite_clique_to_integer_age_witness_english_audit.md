# From every finite L-clique to a normalized integer graph-age witness

**11 November 2026 — English-first proof and adversarial audit.** This note precedes new Lean code. Nothing in this note supplies a full corrected (B3) equivalence or global resolved-copy existence.

## Exact existing APIs

The actual library `Kk/IntegerWitnessCanonical.lean` defines

```lean
abbrev IntegerGraphSupport (d ell : Nat) :=
  {T : Finset (Fin d) // T.Nonempty ∧ T.card ≤ ell - 1}

abbrev IntegerCliqueWeights (d ell : Nat) :=
  {w : Fin d → Fin ell //
    (Finset.univ.sum (fun j : Fin d => (w j).val)) ≤ ell - 1}

def integerCliqueOnSupport {d ell : Nat}
  (w : IntegerCliqueWeights d ell)
  (T : IntegerGraphSupport d ell) : Nat :=
  T.1.sum (fun j => (w.1 j).val)
```

The already merged `Kk/FiniteCliqueSupportWitness.lean` and `Kk/ArbitraryWitnessGluing.lean` quantify over **all directed clique subsets** of a chosen finite future pool `W`, not merely pre-existing selected top originals.

## The correct finite-fiber identity

Let `s : Finset Nat`, `sort : Nat → Fin d`, and `T : Finset (Fin d)`. Define `n_j(s) := |{v∈s : sort(v)=j}|`.

The following two facts have *no* clique or age hypothesis:
[
sum_{j:operatorname{Fin}(d)} n_j(s)=|s|,qquad
sum_{jin T}n_j(s)=|{vin s:operatorname{sort}(v)in T}|.
]
Proof: the fibers of a function partition its finite domain, with each element belonging to exactly one fiber. A finite sum of the fiber indicators counts each element once. The support-restricted identity follows by retaining precisely the fibers whose labels are in T.

**Proof engineering:** Use the *actual Finset cardinality of each filter*, and prove the two identities independently before constructing any subtype. Neither formula may be replaced with the number of distinct sorts: different clique vertices can have equal sort.

## Normalized witness theorem

Fix natural `ell` and assume `s.card < ell`. For each sort j,
[
0le n_j(s)le |s|<ell,
]
so it canonically defines an element `w_j : Fin ell`. The full fiber identity gives
[
sum_j w_j.val=|s|leell-1.
]
Thus `w=(w_j)_j` is a genuine `IntegerCliqueWeights d ell` of the **existing** definition. For every admissible `T : IntegerGraphSupport d ell`,
[
oxed{operatorname{integerCliqueOnSupport}(w,T)
     =|{vin s:operatorname{sort}(v)in T}|.}
]
The proof also works when `s=emptyset`, provided `ell>0`, and preserves multiplicities of repeated sorts.

The statement is constructive even though the base graph can be directed: graph edges are irrelevant to the counting construction. The directed clique assumption is used **only** for applications where `s` is a valid continuation witness.

## Interface with raw graph ages

For an arbitrary raw bound `B : IntegerGraphSupport d ell → Nat` and any finite clique `s` of size below `ell`, the exact support equalities imply
[
orall T,;|{vin s:operatorname{sort}(v)in T}|le B(T)
quadLongleftrightarrowquad
operatorname{WitnessRespects}(operatorname{integerCliqueOnSupport},B,w(s)).
]
By the existing `integerGraphAgeCanonical_preserves_clique_vectors`, **the same** particular normalized vector respects `B` iff it respects the canonical graph age `G_B`. This is the correct forward transfer from a realized finite clique to the normalized integer-age canonicalizer. It does not claim that *all* normalized vectors occur in the given future pool.

A separate consequence useful for the four-pool gluing theorem: if `W` is K_ell-free in the existing exact checker, every directed clique `s⊆W` has `|s|<ell` (capacity bound); hence every clique tested by the physical gluing theorem has a normalized vector and exact support counts. This relies on the **independent W or P∪W K_ell-free test**. Without that test the vector might have total weight ≥ell and cannot be represented by `IntegerCliqueWeights`.

## Adversarial obstruction to the converse

**Do NOT assert that all `IntegerCliqueWeights d ell` are realized by cliques in a fixed W.** Concrete counterexample: `ell=3`, `d=1`, `W=emptyset` with any graph and any sort map. The vector with one unit of the only sort is a valid normalized integer vector but has no representative clique in W. The reverse implication requires a **separate richness/realization hypothesis**, not a finitary algebraic argument. This invalidates an otherwise tempting but false proof of full B3 age equality.

A possible next construction is a finite *disjoint union of typed cliques*, one component for every admissible normalized vector `w`, with exactly `w_j` vertices of sort j in that component. This realizes all normalized vectors in a combinatorial K_ell-free graph, because each component has size ≤ell−1 and different components are nonadjacent. It does **not** automatically preserve old-to-future mixed adjacency or auxiliary E/parameter-closed data in Henson H+, which must be verified separately.

## Independent hostile checks

1. **Multiplicity:** `sort` may map many clique vertices to the same `j`; using `card (sort '' s)` is wrong.
2. **Carrier size:** the bound `s.card<ell` is essential to cast fiber cardinalities as `Fin ell`, and to bound the sum.
3. **Zero threshold:** for `ell=0` no `s.card<ell` exists; never invent a zero element of `Fin 0`.
4. **Empty clique:** for `ell>0`, the empty `s` gives the all-zero normalized vector and correct zero support counts.
5. **Repeated sorts:** support-filter cardinality must equal the *sum* of per-sort counts, not the number of occupied sorts.
6. **All admissible supports:** `IntegerGraphSupport` excludes empty T and bounds T.card by ell−1, but the fiber sum identity holds for any T; restrict only at the API boundary.
7. **Directionality:** the counting map itself does not imply an ordinary-L directed clique; its input must already satisfy the actual full directed clique predicate.
8. **Large cliques:** if the whole future graph W fails the K_ell check, an s with |s|≥ell may exist, so the normalized witness construction cannot cover all s.
9. **One-way implication:** `W=emptyset, ell=3, d=1` refutes surjectivity of realized-clique vectors onto all normalized integer vectors.
10. **Richness versus mixing:** a disjoint-union-of-witnesses realizer does not automatically satisfy prescribed Q-to-future, P-to-future or G-to-future bit columns.
11. **Canonicalizer:** `G_B` preserves constraints of a *given normalized vector* by the existing theorem; it does not construct the corresponding physical finite H continuation.
12. **No parameter shortcut:** neither the ordinary L clique nor its sort-count vector determines the Kpt auxiliary E or full parameter-closed B3 source.

## Formalization gate

Write (A) exact full-support and partial-support fiber sum lemmas, (B) a constructor `IntegerCliqueWeights d ell` for `s.card<ell`, (C) the exact support-count theorem for every `IntegerGraphSupport`, and (D) transfer of this one vector through the existing `WitnessRespects` and `integerGraphAgeCanonical_preserves_clique_vectors`. Include a regression against surjectivity. Use the pinned Lean 4.35.0-rc3 and matching Mathlib locally for the fiber and arithmetic core; then verify the imported Kk module with full `lake build` and exact named standard-only transitive-axiom reports. Keep the manuscript's protected black prose unchanged.

**Remaining after this bridge:** richness of the actual age-continuation source and compatible realized Henson one-point extensions, synchronization of full marked front and auxiliary E/parameter records, canonical graph-age **equality**, and a common labelled inverse-source orbit.