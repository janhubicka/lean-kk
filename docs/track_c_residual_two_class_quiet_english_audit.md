# Track C — split physical residual quietness into early-old and new-final tests

19 November 2026. English-first proof and adversarial audit.

## Two exact residual cases

For a coherent OLD->NEW Kpt index map phi that is injective, define a residual new-live index at c as one absent from the image of OLD-LIVE indices. The verified Track E theorem `kpt_residual_iff_new_final_or_early_old` states that residuality is equivalent to one of two cases:

- NEW FINAL NAME: no old-final index maps to the new index;
- EARLY OLD NAME: there is an old-final index mapping to it whose old live bit at c is false.

These cases are disjoint by definition, and the implication back to residuality requires injectivity. Do not confuse an early old-final name with a newly created final Kpt node.

## Full dependent quietness obligation

For any new-live residual name j, the condition is BOTH:

1. no cut-terminal: lev(newNode j) != c;
2. every genuine complete old/upper raw Kpt L+/E type pair represented by that SAME node at c is present in the old indexed physical crossing relation.

The E64 `KptResidualQuietAtBoringCut` requires both. Define `KptResidualClassQuiet` for one index class C as precisely these two clauses, conditional on (newLive c j=true and C j).

**Theorem:** when phi is injective, `KptResidualQuietAtBoringCut` is logically equivalent to the conjunction of (a) `KptResidualClassQuiet` for NEW FINAL names, and (b) the same for EARLY OLD names.

**English proof.** In the forward direction, both classes imply residuality by E65 and hence inherit both clauses from E64. In the reverse direction, let j be a residual new-live index. E65 splits the residual into the two cases; apply the appropriate class test for both the terminal and complete crossing-pair clauses.

## Adversarial checks

1. Both terminal and crossing tests must be transferred; retaining only I1 terminal absence is insufficient.
2. A crossing pair has old/upper ancestors of ONE physical node; it is not a pair of independently matched old nodes.
3. Full partial types include negative ordinary L, unary/diagonal and auxiliary E information.
4. The result does not rely on I2 functionality or project parameters to a selected graph-age shadow.
5. This is exact for arbitrary finite indexed Kpt sources with a coherent injective map, not a diary statement.
6. Injectivity is required for the reverse classification: noninjective phi can have an early old index and a different old live index both mapping to j.
7. No new physical stage is assumed. A subsequent application should obtain phi from the already verified constructed physical source-index theorem.
8. The NEW FINAL class does not automatically enumerate actual scheduled diary microevents; a geometry lemma must identify its possible nodes.
9. The EARLY OLD class may be nonempty even when the final source-node universes are equal.
10. No class is shown quiet by the splitting theorem: it is an iff reduction.
11. The K4 q2 E cuts 10 and 22 remain in the raw pair tests.
12. Neither a uniform event count nor cross-occurrence monoid inverse-source transport follows.

## Proof engineering

Lean should import `Kk.TrackENumericResidualTwoClass`, reuse its exact residual iff, and introduce just the class-local quietness predicate plus one iff theorem. Do not copy E64/E65 proofs or add independent axioms. Direct #check / #print axioms and a full Lake CI gate are required before integration. Use the resulting lemma with constructed physical source data in a second theorem if it can be derived without adding geometric assumptions.
