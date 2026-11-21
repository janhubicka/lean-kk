# Track F — no hidden mixed age change immediately before a zero-code

21 November 2026. English proof and adversarial audit written **before Lean**. This is the algebraic half of the independent-code paragraph in the frozen K4 history-realization proof. It is independent of the geometric code-vertex selection in PR #424.

## Exact bounded-support statement

Fix finite indexed sorts `Fin(d)`, a forbidden clique size `ell≥2`, and a sort `j:Fin(d)`. Let `F` be the prescribed **precode** normalized integer age and `P` the genuine **actual immediately-before-code** normalized integer age on the identical bounded nonempty support domain `IntegerGraphSupport(d,ell)`.

Assume:

1. `P≤F` pointwise, as required by monotonicity of actual profile refinement from the old checkpoint.
2. `P` is a genuine normalized integer graph age, hence monotone under inclusion of nonempty admissible supports (verified `integerGraphAge_monotone`).
3. Both `P({j})=F({j})=1` (the coded coordinate is manuscript singleton rank one).
4. On every admissible nonempty support `S` **not containing j**, we have `P(S)=F(S)`. This is the survivor profile comparison, already established after the later survivor synchronization (not a result of individual rank matching alone).
5. The precise **legal zero-code condition** holds: on every admissible nonempty support `T` containing j and at least one survivor, `F(T)=F(T\{j})`. This is the manuscript's `F(S∪{j})=F(S)`, restricted to supports in the genuine bounded domain.

**Conclusion:** `P=F` on EVERY admissible nonempty support, including all mixed triple supports. No unrecorded strict profile change can occur immediately before the code, under these geometric/age assumptions.

## Proof

Fix any nonempty admissible support T. If j∉T, equality is exactly assumption (4). If T={j}, equality follows from (3). Otherwise j∈T and `S=T\{j}` is nonempty; it remains admissible since `S⊆T` and T was admissible. Since j∉S, we know `P(S)=F(S)`. Monotonicity of the TRUE age P gives `P(S)≤P(T)`. Legal zero-code gives `F(T)=F(S)`. The old-to-precode refinement bound gives `P(T)≤F(T)`. Hence

`F(T)=F(S)=P(S)≤P(T)≤F(T)`,

so equality holds. Every support T is covered; this includes triples automatically and is not merely pairwise checking.

A single proper support `S=T\{j}` suffices; no additional certificate clique or canonical cover classification is needed at this algebraic step.

## Audit

1. **Monotonicity must be applied to P, not F.** It is the actual precode age whose mixed bound we must show cannot be smaller.
2. **Survivor agreement must cover every nonempty survivor support**, not just survivor singleton ranks/pairs. The triple case can otherwise fail.
3. When T={j}, the erase support is empty and is OUTSIDE the manuscript's age domain. It is dealt with by the two singleton-equality hypotheses, not by inventing F(∅).
4. If d=1, every support containing j is {j}; the proof remains valid and avoids choosing an arbitrary second sort.
5. If ell=2, all admissible supports have size at most one, so the mixed case is vacuous. The singleton {j} is still admissible.
6. For mixed T, S=T.erase j is nonempty and admissible with cardinality at most ell−1, because it is a subset of T.
7. The precise code legality condition is only needed when S is admissible. Do not quantify over non-admissible supports or silently read an undefined F(T).
8. `P≤F` alone is insufficient. If we drop monotonicity, a pointwise smaller mixed P(T) can coexist with unchanged singleton/survivor bounds; it would not be a genuine graph age.
9. `P({j})=F({j})=1` is essential for the singleton case. The code selection of a rank-zero source coding vertex alone does not automatically establish both displayed *target* ages without the separate compatible tuple/rank argument.
10. This lemma is PURE integer-age algebra, without an induced embedding, actual source fibre, target lex order or Kpt auxiliary data.
11. The later survivor synchronization must occur AFTER the selected target code level to deduce survivor agreement at the precode cut by a sandwich. That geometric implication is not assumed to be formalized by this algebraic lemma.
12. The theorem only excludes hidden strict age changes at the precode profile; it does not construct a coding vertex, an actual survivor front, or prove post-code zero columns.
13. It does not decide how the remaining active target types are ordered, and it does not imply that the next diary event is canonical.
14. The graph-age predicate `IsIntegerGraphAge` is the already verified normalized integer-witness class equivalent to the manuscript's unrestricted definition; no new age axiom is added.
15. This lemma does not require F itself to be a genuine age; that is true in the application but mathematically unnecessary for the sandwich. **P must be genuine**, or at least monotone.
16. No completion of all cover/split/code history realization or BRD lower bound follows by itself.

## Lean gate

Formalize the exact domain-correct theorem using `IntegerGraphSupport d ell`, `IsIntegerGraphAge`, `AgeLe`, and `integerGraphAge_monotone`. Encode the zero-code legality by deleting j from the genuine mixed support and matching the resulting actual subtype; never quantify at empty support. Exact-head Lake build and strict named standard-only axiom report before merging. Black manuscript unchanged.
