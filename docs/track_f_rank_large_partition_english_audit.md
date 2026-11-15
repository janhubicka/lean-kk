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

## Next graph-specific obligations

Instantiate the preorder with the *actual* Henson coding tree,
and identify rank `n` with singleton graph age `n+1`.
Prove density implies corresponding `Large` by constructing real
one-step clique certificates; then prove the multi-coordinate
rank-large age-recovery and compatible-pair synchronization lemmas.
Finally construct one prescribed diary in each induced Henson
self-copy. These are the substantial unverified lower-bound steps.
**Do not promote any unconditional BRD validation marker from this note.**
