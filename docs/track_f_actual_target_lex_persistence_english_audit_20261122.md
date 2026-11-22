# Track F — target lexicographic sort order is preserved by genuine chronological refinement

22 November 2026, evening. English proof and hostile audit committed BEFORE Lean.

## Motivation

The frozen manuscript indexes every actual target level front in the ordinary binary lexicographic order 0<1. Source coding-node labels may be in a different lex order under the arbitrary injective induced map e. Track F source/target finite-class synchronization preserves the chosen Fin(d) coordinate labels and complete old bits, but the lower-bound diary proof must justify that those labels remain in TARGET lex order after refinements and code deletion. This is a separate, finite, first-difference invariant; no Ramsey or rank argument is needed.

## Exact first-difference relation

For genuine finite K_ell one-types u,v of the SAME actual target graph E (levels may differ), define

  LexBefore(u,v)  iff
    exists a < level(u), level(v) such that
      [for all b<a, (b∈N(u)) iff (b∈N(v))],
      a∉N(u) and a∈N(v).

This is lex order on the complete 0/1 old-bit words when a first difference lies within both finite prefixes. Zero is earlier than one, so the all-zero type is lexicographically first as in the manuscript.

## Extension invariance

If u≤u' and v≤v' as GENUINE chronological one-types, all positive and negative bits before the original levels are preserved. A witness a for LexBefore(u,v) is still below both later levels, the bits at a remain 0 and 1, and for every b<a the old bit equality remains true in the later pair. Therefore LexBefore(u',v').

The witness is the SAME original coordinate a. No new marker can reverse the earlier first difference, regardless of source-image chronological order or additional positive neighbours beyond the old prefix.

## Finite front invariance

Define IsTargetLexSorted(front:Fin(d)→HensonOneType ell E) to mean:

  for all i<k in Fin(d), LexBefore(front_i, front_k).

Given old and new target fronts on the SAME Fin(d), with each old_i≤new_i, IsTargetLexSorted(old) implies IsTargetLexSorted(new).

For coding deletion at j:Fin(d+1), the actual surviving coordinate injection f=Fin.succAboveEmb j is STRICTLY monotone (checked Mathlib Fin.strictMono_succAbove). Thus for i<k in Fin(d), f(i)<f(k) in the old target order; if the original target front is lex sorted and its actually surviving refined types t_i extend old_{f(i)}, then t is lex sorted too. No reordering of survivors is needed after an independent code (although after a SPLIT two new children must still be named in target lex order).

This addresses one explicit open Track F diary-history ordering gate: the zero-code survivor deletion map indeed tracks the TARGET ordering throughout genuine refinements, not the arbitrary source lex ordering.

## Hostile audit

1. The relation is on the actual binary chronological old-neighbour bits, not on source original indices, generation counters, raw profile numerical ranks, or selected E/parameter labels.
2. It uses alphabet convention 0<1, consistent with the manuscript's claim that all-zero type is lex first.
3. The witness a must belong to BOTH old type domains, a<level(u),level(v), so their later comparisons are guaranteed defined.
4. For b<a, both old bits must agree; otherwise a need not be the first difference. Neglecting this would not represent lex order.
5. Chronological refinement must preserve complete positive AND negative old bits, not merely include positive neighbours.
6. No assumption that the source→target embedding e preserves numerical order or source lex order; these are TARGET graph types throughout.
7. This theorem does not assert two arbitrary old types are comparable if one is an initial prefix of the other. In actual diary fronts types share a common level and are distinct, so comparability is available separately.
8. IsTargetLexSorted is a STRICT condition on i<k. If d≤1 it is vacuous; no arbitrary Fin(0) element is chosen.
9. The survivor injection Fin.succAboveEmb j is strict monotone, not just injective; an arbitrary injection or permutation could change target-sort indexing even if the set of branches remains the same.
10. The new surviving types must refine the corresponding old_{f(i)} individually, not just form a finite multiset of compatible types.
11. This verifies the relative lex ordering of existing survivors across zero coding; it does NOT determine the new daughter order after a split, where both children share one old parent and their first differing bit may appear only at the new pivot.
12. It does NOT prevent previously distinct target types from meeting in the tree (they cannot be equal after genuine extension); it merely preserves a first differing old bit.
13. It does NOT verify full dependent Kpt L+/E history, exact inter-branch meeting events, or global diary record occurrence.
14. No direct big Ramsey degree, independent triple count or 24-orbit enumeration follows.
15. The frozen black manuscript proof remains unchanged; validation annotations should be scoped to the verified lex persistence only.
16. The proof is arbitrary ell and any actual directed edge table E; it does not need symmetry, forbidden-family avoidance or rank largeness beyond genuine one-type construction.
17. The order preservation is the standard binary lex order; reversing the alphabet to 1<0 would reverse the direction of LexBefore, not its extension invariance, but the manuscript's all-zero-first convention fixes 0<1.

## Lean gate

Implement the first-difference LexBefore relation, its invariance under two genuine chronological refinements, finite-front sortedness preservation under coordinatewise refinements, and actual survivor deletion sortedness preservation under Fin.succAboveEmb j using Fin.strictMono_succAbove. Exact-head Lean, named strict standard-only axiom reports, and full CI before merge. No new axioms or global diary statement.
