# Track F — labelled diary fibres are torsors for graph automorphisms

**English proof and hostile review before Lean.** Companion to the independent Track F [age-column proof](track_f_cover_column_english_audit.md); this is a separate, graph-theoretic counting lemma. It is deliberately not a proof of the full diary bijection, nor of the unavoidability theorem.

## Exact lemma

Let (A=(V,R)) be a finite loop-free undirected graph (the argument works more generally for any finite binary relation), let (D) be a finite set of **distinct diary objects**, and let (C_d=(V_d,R_d)) be the coded graph for each (d\in D). Assume a graph isomorphism (h_d:A\cong C_d) for every (d).

Define the set of labelled diary types as the dependent sum
`Σ d:D, GraphIso(A,C_d)`, and the finite group of automorphisms `GraphAut(A):=GraphIso(A,A)`. Then

`|Σ d:D, GraphIso(A,C_d)| = |D| * |GraphAut(A)|.`

### Proof with inverse, avoiding a symmetry assumption

For fixed `d`, compose an automorphism `a:A≅A` *after* the source and *before* the fixed isomorphism `h_d:A≅C_d`. This gives `a ↦ h_d ∘ a`, a graph isomorphism `A≅C_d`. Its inverse sends `g:A≅C_d` to `h_d^{-1}∘ g`. Both composites are the identity by associativity, inverse cancellation and extensionality of graph isomorphisms. Thus every fibre has exactly `|Aut(A)|` elements. Sum over the actual, distinct diary index type D.

No canonical *choice* of `h_d` is needed for cardinal equality; the assumption of a witness for each nonempty fibre suffices, and each actual witness produces an explicit equivalence.

## Adversarial warnings

1. **Do not count arbitrary bijections.** Every map is a graph isomorphism preserving *both* edges and nonedges (`R(x,y) iff R'(f(x),f(y))`); plain `Equiv V V_d` would give `|V|!` and is wrong for the three-vertex path.
2. **No quotient trick.** The statement counts a set of *distinct* diary objects D. If a counter quotients distinct diaries by extra symmetries or counts orderings more than once, this counting lemma does not repair that bug.
3. **Dependent carriers matter.** The coded graph's vertex set may depend on the diary; the lemma uses a dependent sum with a different isomorphism fibre at each diary.
4. **Automorphism size not factorial by default.** `Aut(P3)` has order 2, `Aut(K3)` has order 6, as checked independently by the Track F brute-force program.
5. **Finite only.** `Fintype` is assumed for the source, diary family, and all coded carriers. Published diary finiteness is an independent theorem, not supplied here.
6. **No BRD conclusion.** A cardinality identity says nothing about which types persist in each subcopy. Published Theorems 3.4.12 and 3.4.14 provide an external unavoidability route, not derived from this lemma.
7. **Proof-irrelevant fields.** A graph isomorphism with a binary relation biconditional is a structure containing an underlying equivalence plus proof. Extensionality must identify two isomorphisms whenever their underlying equivalences coincide.

### Formalization target

Use actual finite binary relational isomorphisms `BinaryRelIso R S`, their `trans` and `symm`, a fibre equivalence `BinaryRelIso R R ≃ BinaryRelIso R S`, and `Fintype.card_sigma`. Require a targeted compiled module and standard-only transitive axiom checks before any validation mark.
