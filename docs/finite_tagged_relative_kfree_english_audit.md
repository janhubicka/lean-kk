# Track A — exact finite relative free-amalgam compatibility of a tagged universal future

**14 November 2026. English proof and adversarial checks BEFORE Lean.**
Stacked over the independent exact-Nat encoder PR #147.
This is the combinatorial missing step between the standalone
universal future graph and one fixed Henson old-prefix embedding.

## Input

Let E be any directed Boolean graph table on Nat, b a fixed
old-prefix cutoff, ell a forbidden-clique size, d>=1 a number of
future types, c(p,t) the COMPLETE prescribed old-to-future
L column for every old p<b and future sort t∈Fin d.
Write P=[0,b) and define the literal old reference raw bounds

    B_P(T)=ell-1-
       finiteDirectedCliqueCapacity E
         {p∈P : ∀t∈T,c(p,t)=true},

for each admissible nonempty support T.

Let V be any finite type, R:V×V→Bool a finite **directed**
future edge table and sort:V→Fin d. Assume:

- E|P has no K_ell, checked with the real finite clique test;
- every directed R-clique s⊆V has |s|<ell;
- for every directed R-clique s and every admissible T,
  |{v∈s:sort(v)∈T}|≤B_P(T).

Do NOT assume that the entire future set V is a clique.
It may be the disjoint union of all feasible normalized
witness components, with different components nonadjacent.

Using the already encoded *exact* interval [b,b+card V)
and old/future table A_b from PR #147, define
`W_b=code_b(V)` and the total future sort map
`tau_b(z)=sort(decode_b(z))` on W_b.

## Conclusion

The **entire combined target** A_b on the literal consecutive
prefix [0,b+card V) is K_ell-free, and all of its old/future
crossing bits match c in BOTH ordered directions. In particular
this is a genuine relative finite K_ell-free extension of
the exact old prefix E, not a standalone abstract future.

This theorem does not require E symmetric, nor the finite R
symmetric, for the purely directed clique-freeness calculation;
the Henson application additionally requires those properties
to invoke the pinned induced extension theorem.

## Proof

### Finite image transport

The code_b injection from PR #147 is exact on all V.
For every finite s⊆V:

1. s is a directed R-clique iff code_b(s) is an
   A_b-directed clique. This uses ALL ordered off-diagonal
   future bits, not one orientation.
2. Its cardinality is unchanged.
3. For every support T, the count of tau_b-labels in
   code_b(s) equals the count of sort-labels in s.

Conversely every subset q⊆W_b is code_b(s) for the finite
pullback s={v∈V:code_b(v)∈q}; the same clique and
support-count identities hold. Thus A_b|W_b has no
forbidden clique, and every actual future clique
satisfies the same complete raw support bound B_P.

### Old-prefix raw bound comparison

On P×P, A_b(x,y)=E(x,y) literally for both ordered
off-diagonal atoms, by the verified encoder. Hence the
finite old common-neighbour pool R_P(T) has EXACTLY
the same directed clique capacity in A_b and in E,
by the checked identity-induced capacity transport.
Therefore the raw bound computed from A_b's old
prefix is pointwise equal to B_P; no hidden
old-graph relabelling or stronger symmetry assumption.

### Full gluing

P∩W_b=empty, and P∪W_b is **exactly**
[0,b+card V). Old P is K_ell-free in A_b
by old-table equality; the new W_b is K_ell-free
by future clique transport. Every P→W_b and
W_b→P bit is exactly c(p,tau_b(w)).
Now apply the ALREADY VERIFIED
`finiteOldFuture_free_of_all_raw_support` to A_b
with P,W_b,c and all raw support constraints.
It proves the entire literal target prefix is K_ell-free.

## Hostile audit

1. **No cardinal shortcut.** Common old neighbours need
   not be a clique; use their actual maximum *directed*
   clique capacity.
2. **Mixed supports essential.** A future graph satisfying
   only the selected singleton bound can create a
   forbidden mixed K_ell with an old clique adjacent
   to two different future types. Quantify over EVERY T.
3. **All original old vertices included.** P=[0,b)
   is the entire fixed prefix, not selected past alone;
   old gaps may form mixed cliques.
4. **Two-direction crossing.** The gluing theorem needs
   both A_b(p,w) and A_b(w,p), checked by separate
   encoder lemmas.
5. **Empty future type V.** Then W_b=empty and A_b|P=E;
   the theorem follows from old K_ell-freeness without
   a default V element.
6. **No d=0 default.** The total Nat future-sort map
   requires d>0. A separate empty-sort trivial case
   could be proved, but no element of Fin 0 is fabricated.
7. **No fake future labels.** Code_b(V) is EXACTLY
   [b,b+card V), so the union P∪W_b has no holes
   inside the target range. Later physical Henson
   gaps arise only during the pinned embedding.
8. **No automatic symmetry.** Pure K_ell-freeness
   works for directed R; the actual Henson application
   must instantiate R with the verified symmetric,
   loop-free universal witness graph.
9. **No automatic nonspurious vector inference from
   positivity.** All support inequalities are
   checked for EVERY directed finite clique s,
   not merely the full future or any one component.
10. **No global source E/B3 conclusion.** Ordinary
    L join is separate from auxiliary Kpt E and
    full parameter-closed source orbit.
11. **No complete infinite resolution.** This proves
    existence of a finite *compatible target* when
    V,R,sort satisfy the finite raw profile; the
    pinned Henson theorem next embeds that target
    once into the fixed original graph. It does not
    produce an unbounded coherent recursive diary.
12. **Canonical vs raw.** The gluing uses B_P raw
    bounds; after Kfree, the checked joint
    canonicalizer yields exactly the same labelled
    clique profile. Never identify raw B_P with
    its canonicalizer pointwise.

## Specialization needed next

Take V to be the finite subtype of vertices of
`universalWitnessFuture d ell B_P`, with future
R induced by `universalWitnessEdge` and sort
from `v.1.2.1`. The checked
`UniversalFutureDisjointCliques` theorems yield
the two exact input conditions and realize every
B_P-feasible normalized vector in one finite V.
The present gluing lemma then builds Kfree A_b.
Combining with PR #137's pinned uniform finite
Henson embedding closes the **finite uniform
relative age** statement over any fixed old
prefix in the actual left-dense Henson original E.
All global resolved-stage/auxiliary source
invariants remain independent.

## Acceptance

New `Kk/FiniteTaggedRelativeKFree.lean`, importing
the verified encoder + old-column age + finite
capacity transport. Independent exact-head
compilation, fully qualified named standard-only
transitive-axiom check and full `lake build`.
No changes to central Lean aggregator, manuscript
marks or frozen black manuscript sections.
