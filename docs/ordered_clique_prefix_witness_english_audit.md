# Track A — extracting an increasing original clique below the current name

16 November 2026. English proof and adversarial audit **before Lean**.

## Mathematical statement

Let E be an arbitrary directed Boolean adjacency table on natural names.
Let S be a finite set of originals, all STRICTLY below b, and suppose
E(i,b)=true for every i∈S. Let
  c = finiteDirectedCliqueCapacity E S.
For any a≤c, there is a total name map q:Nat→Nat with

  q(a)=b;
  q(i)∈S for every i<a;
  q(i)<q(j) for every i<j<a+1;
  E(q(i),q(j))=true for every i<j<a+1.

No symmetry assumption on E is needed; directed-clique positivity is
available for all ordered distinct pairs inside the chosen clique C,
and original-to-b positivity is assumed in the correct orientation.
The q values for i>a are arbitrary (choose b).

## Proof

The independently checked finite-directed-capacity attainment theorem
provides a directed E-clique C⊆S with cardinal c.

Because a≤C.card, let p:Fin C.card ↪o Nat be the strictly increasing
enumeration supplied by Finset.orderEmbOfFin rfl. It is injective,
and its values all belong to C. Define, for all n∈Nat,

   q(n)=p(n) if n<a, and q(n)=b otherwise,

where the first case regards n as Fin C.card using n<a≤C.card.

For n<a, q(n)∈C⊆S and hence q(n)<b, while q(a)=b.

If i<j<a, both names are enumerated by the strict order embedding p,
so q(i)<q(j). Both lie in the original E-clique C and are distinct,
hence E(q(i),q(j))=true.

If i<a and j=a, strict order follows from q(i)∈S⊆[0,b),
and E(q(i),q(a))=E(q(i),b)=true by hypothesis on S.
No other cases satisfy i<j<a+1. Therefore q satisfies all four
requirements.

This method avoids an additional "extract a subset of cardinal a"
lemma: the first a terms of the full maximum-clique ordered enumeration
are already an increasing a-clique. It also covers a=0 (q(0)=b),
c=0, and nonconsecutive elements of S.

## Hostile checks

1. c is **clique capacity**, not |S|.
2. Exact capacity attainment is used, not an assumed realizing clique.
3. The ordered enumeration p is on C, not on S: S need not be a clique.
4. The finite original names are in Nat and are ordered by their
   fixed Henson enumeration; no relabelled graph replaces E.
5. Every C member is <b, so appending b is strictly increasing.
6. Every C member has the positive **forward** E(i,b) atom.
7. Symmetry of E is not assumed for this lemma; in applications
   to Henson graphs it is independently available.
8. The appended index is a, not C.card unless a=c.
9. For a<c the unused tail of C is intentionally ignored.
10. q is a *total* Nat→Nat function, with all later indices set
    to b, but its properties are asserted only for indices ≤a.
11. The case a=0 works without requiring S nonempty.
12. The case S=∅ gives c=0 and forces a=0.
13. Repeated vertex names cannot occur among q(0),...,q(a)
    because p is strictly increasing and b lies after S.
14. The E clique condition on C is the full ordered directed one;
    it provides E(x,y)=true when x<y are distinct members of C.
15. No numerical-H generation gate is used here. That belongs
    to the independently proved physical staircase lemma #241.
16. The eventual choice a=min(c,g-1) for g>0 uses arithmetic
    and will be composed with the conditional numerical staircase;
    this lemma itself does not rely on g.
17. No proof about a coherent recursively prescribed infinite
    selected-original schedule, Kpt auxiliary E/B3, or labelled
    occurrence source follows.

## Lean acceptance

Implement a standalone Kk/OrderedCliquePrefixWitness.lean starting from
the existing capacity-attainment theorem, Finset.orderEmbOfFin and
its membership/strict-monotonicity lemmas. Prove the exact four
properties and print the fully qualified theorem axioms. Require
exact-head direct module build, strict standard-only named-axiom
check and full Lake build. This proof is independent of the
partially certified numerical-H PR stack, and can be merged separately.
