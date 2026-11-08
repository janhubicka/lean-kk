# Exact finite gluing with an isolated reserved block

## Status and implementation boundary

This English proof and adversarial audit are written before the proposed
Lean implementation. The intended source module is
Kk/IsolatedBlockContinuationAge.lean. The English document must be committed
first, and independent review must precede implementation.

This is a finite graph theorem using the repository's existing Boolean
edge tables, finite-set clique checker, and exact clique capacity. It does
not construct numerical-H originals, establish simultaneous marked columns,
identify an integer graph-age function, or prove a global resolved copy.
No Lean process was run while preparing this plan.

The intended implementation consists of the four public endpoints below.
It introduces no new definition of closure, age, or graph admissibility,
and no predicate that assumes the desired selected-age conclusion.

## Fixed representations and conventions

Fix an arbitrary Boolean table

```lean
E : Nat → Nat → Bool
```

The existing predicate IsDirectedCliqueOn E s means

```lean
∀ x ∈ s, ∀ y ∈ s, x ≠ y → E x y = true.
```

It tests both ordered orientations of every distinct pair and ignores
diagonal entries. The empty set and every singleton are cliques. Global
symmetry and loop-freeness are unnecessary for the generic theorem.
When applying the result to ordinary K_ell-free graphs, the actual L-table
is separately known to be symmetric and irreflexive; the directed clique
test then agrees with the ordinary graph clique test. The generic theorem
does not by itself certify avoidance of separate loop/asymmetry patterns.

The existing finitePoolCliqueCheck E ell A is true exactly when A
contains a clique of cardinality ell. The existing
finiteDirectedCliqueCapacity E A is the maximum cardinality of a clique
subset of A, computed as a finite supremum over its powerset. The empty
subset ensures that this maximum always exists, even when A is empty.

For the main result, P,Q,G,W are pairwise disjoint finite sets:

- P contains the old prefix vertices.
- Q contains the inserted reserved vertices present at the tested cut.
- G contains all other inserted past vertices, including unused gaps.
- W contains the future continuation vertices.

The concrete subset U of W contains those future vertices whose marked
labels belong to the prescribed support. At this finite stage U is simply
a Finset, with an explicit inclusion U subset W. No source-representation
oracle or age predicate is introduced.

Use the same E for the entire union. Thus the edge table on P union W
is literally the restriction of the full table, with every internal
future edge retained. The theorem permits arbitrary internal edges of W.

## Theorem 1: finite capacity is attained

Proposed exact signature:

```lean
theorem finiteDirectedCliqueCapacity_attained
    (E : Nat → Nat → Bool) (P : Finset Nat) :
    ∃ s : Finset Nat,
      s ⊆ P ∧
      IsDirectedCliqueOn E s ∧
      s.card = finiteDirectedCliqueCapacity E P
```

### English proof

Let C be the finite family obtained by filtering P.powerset for the
existing directed-clique predicate. The empty set belongs to C, so C is
nonempty. Apply Finset.exists_mem_eq_sup to C and Finset.card. It supplies
s in C whose cardinality equals the finite supremum defining the capacity.
Unpack membership in the powerset and its filter to obtain s subset P
and the clique property. This also works when P is empty: then s is empty
and the capacity is zero.

No positive-capacity premise or chosen maximum-clique oracle is needed.

## Theorem 2: the exact checker-capacity equivalence

Proposed exact signature:

```lean
theorem finitePoolCliqueCheck_false_iff_capacity_lt
    (E : Nat → Nat → Bool) (ell : Nat) (P : Finset Nat) :
    finitePoolCliqueCheck E ell P = false ↔
      finiteDirectedCliqueCapacity E P < ell
```

### English proof

If capacity is less than ell, an ell-element clique in P would contradict
directedClique_card_le_capacity. The existing
finitePoolCliqueCheck_false_iff converts this absence of a witness into
the negative Boolean result.

Conversely, suppose the checker is false but capacity is at least ell.
Choose an attaining clique s by Theorem 1. Apply
Finset.exists_subset_card_eq to extract a subset t of s with cardinality
ell. A subset of a directed clique is a directed clique, and t subset P.
This contradicts the existing negative-checker equivalence.

The signature deliberately allows ell=0. Every P has the empty
zero-clique, so the checker is true, while capacity<0 is false. Both sides
of the displayed equivalence are therefore false in this boundary case.
No hidden positivity premise is required.

## Theorem 3: exact capacity of a complete join

Proposed exact signature:

```lean
theorem finiteDirectedCliqueCapacity_complete_join
    (E : Nat → Nat → Bool) (Q U : Finset Nat)
    (hDisjoint : Disjoint Q U)
    (hJoin :
      ∀ q ∈ Q, ∀ u ∈ U,
        E q u = true ∧ E u q = true) :
    finiteDirectedCliqueCapacity E (Q ∪ U) =
      finiteDirectedCliqueCapacity E Q +
        finiteDirectedCliqueCapacity E U
```

### English proof

For the upper bound, let s be any clique in Q union U. Its intersections
s intersect Q and s intersect U are cliques. Their cardinalities are
bounded by the capacities of Q and U respectively. Their union is s,
so s.card is at most the sum of those two capacities. Take the defining
finite supremum over s.

For the lower bound, choose capacity-attaining cliques q in Q and u in U.
They are disjoint. Their union is a clique: internal ordered pairs are
handled by the two clique properties, and crossing ordered pairs by the
two parts of hJoin. Its cardinality is q.card+u.card, which is the desired
sum. Apply directedClique_card_le_capacity to this concrete union.

Neither Q nor U itself is required to be a clique. This matters in the
numerical-H application, where Q may contain many nonadjacent generation
copies of the same original. Using Q.card in place of its clique capacity
would generally lose the exact equivalence needed below.

## Theorem 4: exact isolated-block continuation test

Proposed exact signature:

```lean
theorem finitePoolCliqueCheck_isolated_block_gluing_iff
    (E : Nat → Nat → Bool) (ell : Nat)
    (P Q G W U : Finset Nat)
    (hPQ : Disjoint P Q)
    (hPastG : Disjoint (P ∪ Q) G)
    (hPastW : Disjoint ((P ∪ Q) ∪ G) W)
    (hU : U ⊆ W)
    (hNoPQ :
      ∀ p ∈ P, ∀ q ∈ Q, E p q = false)
    (hNoGW :
      ∀ g ∈ G, ∀ w ∈ W, E g w = false)
    (hSupport :
      ∀ q ∈ Q, ∀ w ∈ W,
        E q w = decide (w ∈ U) ∧
        E w q = decide (w ∈ U))
    (hPast :
      finitePoolCliqueCheck E ell ((P ∪ Q) ∪ G) = false) :
    finitePoolCliqueCheck E ell (((P ∪ Q) ∪ G) ∪ W) = false ↔
      finitePoolCliqueCheck E ell (P ∪ W) = false ∧
        finiteDirectedCliqueCapacity E Q +
          finiteDirectedCliqueCapacity E U < ell
```

The three disjointness hypotheses express the four-part partition using
existing Finset notions. In particular they imply Q is disjoint from U,
using hU. They also make all cross-part vertices distinct when invoking
the clique predicate.

Only one absent orientation is required in hNoPQ and hNoGW: a complete
directed clique would require that very orientation to be positive.
Both positive orientations across Q and U are required and are supplied
by hSupport. Its absent bits also exclude every future vertex outside U
from any clique meeting Q.

There are no restrictions on P-G or Q-G edges. Cliques wholly in the past
are handled by hPast; cliques meeting W cannot use G.

### English proof: classification of all possible cliques

Write Past=(P union Q) union G and V=Past union W. Let s be a directed
clique with s subset V.

1. If s has no member in W, then s subset Past.
2. Otherwise choose w0 in s intersect W. No vertex of s can belong to G:
   such a vertex g differs from w0 by disjointness, so the clique requires
   E g w0=true, contradicting hNoGW.
3. If this s has no member in Q, every member lies in P union W.
4. Otherwise choose q0 in s intersect Q. No member can lie in P:
   hNoPQ contradicts the ordered edge from that member to q0. Each
   member w in s intersect W belongs to U, because the positive edge
   E q0 w and hSupport force decide(w in U)=true. Hence s subset Q union U.

Thus every clique is contained in one of the three actual sets
Past, P union W, or Q union U. The sets may overlap in this classification;
no uniqueness assertion is needed. Each is itself a subset of V.

### English proof: equivalence

Suppose the full checker is false. Restricting a hypothetical ell-clique
from P union W to V shows that its checker is false. The same argument
shows that Q union U has no ell-clique. Theorem 2 and then Theorem 3,
using the join supplied by hSupport, give

$$
\operatorname{cap}(Q)+\operatorname{cap}(U)<\ell.
$$

Conversely, assume the two conclusions on the right. If an ell-clique
existed in V, classify it as above. The Past case contradicts hPast.
The P union W case contradicts the first negative checker. In the
Q union U case, its cardinality is at most the sum of the two capacities
by Theorem 3, contradicting the displayed strict bound. The existing
negative-checker equivalence concludes the proof.

This derives the exact finite continuation obstruction from actual
L-atoms and partition data. It never assumes that only the desired
age constraint is imposed.

## API inventory checked in the existing sources

| Task | Existing API | Source |
|---|---|---|
| Directed clique predicate | IsDirectedCliqueOn | Kk/OnePointCliqueExtension.lean, line 26 |
| Finite-pool Boolean check | finitePoolCliqueCheck | Kk/LaterSelectedExactMixing.lean, line 31 |
| Positive and negative checker witnesses | finitePoolCliqueCheck_true_iff; finitePoolCliqueCheck_false_iff | Same file, lines 36 and 53 |
| Exact finite clique capacity | finiteDirectedCliqueCapacity | Kk/LinkedCliqueCapacity.lean, line 36 |
| Bound any concrete clique | directedClique_card_le_capacity | Same file, line 43 |
| Capacity monotonicity | finiteDirectedCliqueCapacity_mono | Kk/LinkedCliqueCapacityUpdate.lean, line 35 |
| Attainment of a nonempty finite supremum | Finset.exists_mem_eq_sup | Mathlib/Data/Finset/Lattice/Fold.lean, line 774 |
| Extract a subset of prescribed smaller size | Finset.exists_subset_card_eq | Mathlib/Data/Finset/Card.lean, line 677 |

The expected imports are Kk.LinkedCliqueCapacityUpdate and Mathlib.Tactic.
They supply the existing clique/checker/capacity definitions transitively.
Finset.sup_le, Finset.le_sup, the powerset/filter membership equivalences,
and the finite union-cardinality lemmas supply the remaining bookkeeping.

The existing mixed-neighbourhood modules validate the general pattern of
classifying a clique by the block it meets. Their particular tagged-block
and one-point-neighbour interfaces need not be imposed here: the four
actual finite sets directly describe this gluing problem.

## Adversarial checks

1. **Zero threshold.** At ell=0 every pool contains the empty clique,
   so Theorem 2 is still exact. In Theorem 4 the explicit hPast premise
   is then impossible. No positive-threshold argument is silently used.
2. **Threshold one.** Every singleton is a directed clique, independent
   of diagonal entries. The same proofs remain valid; application to
   Henson graphs normally uses ell>=3.
3. **Empty pools.** Capacities of empty sets are zero, and the capacity
   family remains nonempty. The complete-join theorem works if either
   side is empty.
4. **Empty Q.** The support condition becomes vacuous. The additional
   capacity bound reduces to cap(U)<ell, already forced by freeness of
   P union W because U subset W. No spurious new restriction appears.
5. **Empty W.** Then U is empty. Full freeness is exactly hPast; both
   right-hand conditions follow by restriction of the past.
6. **Empty U.** All Q-W bits are zero. The extra scalar condition
   reduces to cap(Q)<ell, already supplied by hPast.
7. **Q need not be complete.** Its actual maximum clique size, not its
   number of vertices, is used. Two nonadjacent Q vertices joined to
   one U vertex have join capacity two, not three.
8. **Both positive orientations are essential.** With Q={q}, U={u},
   E q u=true and E u q=false, the union has directed capacity one,
   while the sum is two. The stated hJoin and hSupport exclude this.
9. **Outside-support zeros are essential.** For ell=3, let P and G be
   empty, Q be a singleton, W be an edge, and U be empty. If Q were
   allowed to join W despite U being empty, the full graph would be a
   triangle although the old-plus-future test and proposed sum bound
   would pass.
10. **Old-block isolation is essential.** A triangle p-q-w with
    P={p}, Q={q}, W=U={w} has free past and free P union W and capacity
    sum two. The forbidden P-Q edge is exactly what hNoPQ excludes.
11. **Gap zeros must cover all future vertices.** A gap vertex joined
    to both endpoints of a future edge creates the analogous triangle.
    hNoGW quantifies over every w in W, not just one designated target.
12. **The whole actual gap range must be included.** In an application,
    G must contain every past vertex outside P and Q up to the tested
    cut. If that cut extends past the last reserved original, later
    unused originals must also be included and satisfy hNoGW. Omitting
    them would fail the adapter's partition equality.
13. **Past freeness is independent.** The scalar bound and old-plus-
    future test do not constrain a forbidden clique contained in G
    or a mixed P-Q-G past configuration. hPast is therefore necessary.
14. **The threshold is strict.** Capacity sum equal to ell already
    supplies an ell-clique in the join, using attaining cliques and,
    if needed, subset extraction.
15. **Disjointness is used.** It justifies cross-part vertex inequality
    and addition of the two attaining clique cardinalities. It cannot
    be dropped merely because the sets have different names.
16. **The source graph is not the future graph.** The internal table on
    W is arbitrary. This result does not freeze future-future edges
    to those of the original names representing their marked types.

## Remaining adapters and validation contract

After this finite theorem is proved, an application to the physical
selected-front problem must still:

- Construct the glued finite L-table and prove that P,Q,G,W really
  partition its actual past and future carrier.
- Derive hSupport and hNoGW from simultaneous complete columns for
  every marked front sort, including all relevant gaps.
- Compute the capacity of the actual numerical reserved-copy prefix;
  the proposed isolated-block formula is c(a,g)=a for g<a and a+1
  for g>=a, with 0<=a<r and 0<=g<=k, under the height condition
  k>=r-1. The canonical application uses k=ell and 1<=r<=ell-2.
  Without this height condition, g=k<a is an exception caused by the
  equal-top-generation gate. This numerical calculation is not a
  premise-free consequence of the generic gluing theorem.
- Relate the resulting class of finite labelled continuations to the
  integer graph-age canonicalizer and then apply the existing cover
  theorem when its hypotheses hold.

No global construction, AlgorithmRun selection, auxiliary parameter
closure, or common labelled source conclusion follows from these four
finite endpoints alone.

Implementation should retain the four exact contracts above, reuse the
existing definitions, and register every public endpoint in the strict
named transitive-axiom audit. Report kernel verification only after the
complete required build and audit succeed, with only the repository's
allowed standard Lean axioms.
