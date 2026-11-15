# Independent lower-bound Track F: rank-largeness finite-partition lemma

15 November 2026. **English-first proof and adversarial scope audit.**
This note is independent of the published diary characterization and of
Definition 3.1 of the KK-free manuscript.

## Exact abstract interface

Let `(N,≤)` be a preorder of coding-tree nodes, where `u≤v`
means that `v` extends `u`. Let `r:N→ℕ` be **antitone**
(`u≤v ⇒ r(v)≤r(u)`); rank zero represents the minimal
singleton graph-age rank one.

For a set `S⊆N` of coding nodes define recursively:

- `Large(0,S,u)` iff for every `v≥u` some `w≥v` is in `S`.
- `Large(n+1,S,u)` iff for each `v≥u` of rank `n+1`
  there is `w≥v` of rank `n` with `Large(n,S,w)`.

This definition deliberately **does not** assert that `u` has rank
`n`; theorems needing it explicitly assume `r(u)=n`.
Only reflexivity, transitivity, and rank antitonicity are needed.

## Two-colour theorem and proof

**Theorem.** Suppose `r(u)=n` and `Large(n,A∪B,u)`.
Then one of `A,B` is `n`-large above some `v≥u`
with `r(v)=n`.

Induct on `n`. If `A` is already `n`-large above any
same-rank descendant, take that descendant.

Otherwise `A` is not `n`-large above `u`.
For `n=0`, the failure of density gives `v≥u` such
that no descendant of `v` lies in `A`. Since `A∪B`
is dense above `u`, `B` is dense above `v`.
Antitonicity and `r(u)=0` imply `r(v)=0`.

For `n=m+1`, failure of `A`-largeness gives a
same-rank `v≥u` such that no rank-`m` descendant
`w≥v` has `Large(m,A,w)`. Given any same-rank
`t≥v`, use largeness of `A∪B` to reach rank-`m`
`w≥t` with `Large(m,A∪B,w)`. Apply the induction
hypothesis below `w`: the `A` alternative is excluded
by the chosen `v`, so some rank-`m` `z≥w` has
`Large(m,B,z)`. This is exactly `Large(m+1,B,v)`.
Every extension and rank equality is explicit.

**Finite partition theorem.** For any finite colour type `κ`
and `c:N→κ`, if `r(u)=n` and `S` is `n`-large
above `u`, there is a colour `j` and a same-rank
descendant `v` such that
`{w∈S | c(w)=j}` is `n`-large above `v`.

Proof: induct on the finite palette, splitting its colour-restricted
set into the first colour and all remaining colours and invoking the
two-colour theorem. The empty-palette case is impossible: by
induction on rank, `Large(n,S,u)` with `r(u)=n`
always yields a node of `S` extending `u`.
Nothing about the Henson graph or a particular diary is used.

## Adversarial checks

1. **Antitonicity is necessary.** Take a root of rank zero and
   two incomparable terminal children of rank one. Colour the children
   differently; their union is dense, but neither colour is dense at
   the only rank-zero node.
2. **Rank of the witness is fixed:** a colour-large cone must begin
   at a descendant still of rank `n`, not an arbitrary lower-rank cone.
3. **No cone cofinality assumption is smuggled in:** the induction
   uses only the given `Large` predicate, not an external tree
   density or branching theorem.
4. **The failure witness is uniform:** at successor rank, it excludes
   the first colour at *every* next-rank descendant of one chosen
   same-rank `v`; excluding it at just one `w` would not suffice.
5. **The empty colour set is handled:** largeness and the source
   rank equality force an actual member of `S`.
6. **Noninjective colours and duplicate colour fibres are harmless.**
7. **A preorder is sufficient:** antisymmetry, meets and canonical
   parent nodes are not used.
8. **No artificial existence axiom for rank-drop witnesses:** each
   rank-drop witness used by the proof comes from the assumed
   largeness of the union.
9. **No use of a published diary BRD formula:** this is a primitive
   finite-colouring lemma, not a theorem about the number of diaries.
10. **No inference of unavoidable occurrence:** largeness of selected
    Henson coding-node fibres, their compatibility, age synchronization
    and one-diary embedding still require independent proofs.

## Two further elementary lemmas (English first, 15 November)

**Monotonicity in the selected coding-node set.** If `S⊆T`,
then `Large(n,S,u) ⇒ Large(n,T,u)` at every rank and node.
Proof by induction on `n`: at rank zero retain the same density
witness; at successor rank retain each rank-drop witness and apply
the induction hypothesis to its recursively large cone. No rank
assumption or antitonicity is needed.

**Density implies rank largeness given actual rank drops.** Suppose
for every node `v` of positive rank `n+1`, there is a REAL
extension `w≥v` of rank `n`. If `r(u)=n` and `S`
is dense above `u`, then `Large(n,S,u)`. Induct on `n`.
The base is density. At successor rank, fix a same-rank
`v≥u` and choose its genuine rank-drop extension `w`.
Density above `u` remains density above `w`, so the
induction hypothesis makes `S` recursively large at `w`.

**Necessity of the rank-drop assumption:** A one-node preorder
of rank 1 and `S={u}` is dense, but `Large(1,S,u)`
fails because it has no rank-0 extension. In the Henson
application the rank-drop premise must be proved by real finite
clique-certificate extensions; it must not be postulated as an
unexamined diary axiom.

These two theorems are primitive bookkeeping and do not supply
the graph-specific rank-drop hypothesis or any lower BRD statement.

## Finite deletion without assuming false abstract branching (15 November continuation)

The manuscript also needs to remove finitely many unwanted coding nodes
without losing rank largeness. This requires an *escape hypothesis*; it is
not a consequence of the ranked-preorder axioms alone. For example, in the
one-node preorder at rank zero, the singleton set is dense and hence
large. Therefore a declaration that **no finite set is large in every
ranked preorder** would be false.

Here is the precise standalone English route, with the source rank fixed
to `n` throughout.

1. **Avoidable cone is not large.** Suppose `r(u)=n` and there is
   `v≥u` of rank `n` whose entire cone avoids `F`. Then `F` is
   not `n`-large above `u`. Indeed largeness transfers to `v`;
   the already proved `large_has_member` would then produce a member
   of `F` above `v`, a contradiction.

2. **Subtract a nonlarge set.** Suppose `S` is `n`-large above
   `u` of rank `n`, and `F` is not `n`-large above *any*
   rank-`n` extension of `u`. The cover
   `S⊆(S\F)∪F` and set monotonicity make the union `n`-large.
   The exact two-colour partition theorem finds a same-rank descendant
   on which either `S\F` or `F` is `n`-large.
   The second case contradicts the uniform nonlargeness assumption.

3. **Cone-escape consequence.** If from every rank-`n` descendant
   of `u` there is a further same-rank descendant with a whole cone
   disjoint from `F`, then the preceding two results show that
   `S\F` is `n`-large on some rank-`n` descendant of `u`.
   This is the exact nontrivial order-theoretic part of finite avoidance.

**Hostile checks:** (a) same rank is essential when applying
`large_has_member`; (b) existence of *one* avoiding cone is not
enough to show `F` is nowhere large; (c) finite cardinality by itself
does not imply the cone-escape property in an arbitrary preorder;
(d) antitonicity is used at the partition step, not in the first
avoidance lemma; (e) there is no assumption that `F` itself is
downwards closed; (f) this argument does not import any diary or
big-Ramsey-degree theorem.

For actual Henson coding nodes, proving same-rank zero-padding far
beyond every element of a *finite* forbidden coding-node set yields the
cone-escape premise. That geometric padding statement is still open
as a separately verified Lean application. This new abstract deduction
is therefore a **conditional component**, not a certification of the
manuscript's finite-deletion claim on Henson nodes.

## Next graph-specific obligations

Instantiate the preorder with the *actual* Henson coding tree,
and identify rank `n` with singleton graph age `n+1`.
Prove density implies corresponding `Large` by constructing real
one-step clique certificates; then prove the multi-coordinate
rank-large age-recovery and compatible-pair synchronization lemmas.
Finally construct one prescribed diary in each induced Henson
self-copy. These are the substantial unverified lower-bound steps.
**Do not promote any unconditional BRD validation marker from this note.**
