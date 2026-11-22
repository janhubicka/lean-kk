# Track F — pre-code target front from ONLY the actually surviving target tuple

22 November 2026, evening. English proof and adversarial audit BEFORE Lean.

## API repair

The verified true pre-code front constructor in merged Lean PR #470 takes a full later target family on Fin(d+1), even though the code branch j is TERMINATED and the truly surviving target types only live on Fin(d). The constructor never reads the later j entry except to check its level exceeds the actual code image c=e(r). This adapter removes the fake future branch from the output, the hypotheses, and the subsequent age proof.

Fix genuine normalized K4-free target E, an actual source node x in the real sourceCodingFibre of old target code type old_j, a genuine distinct old target tuple old:Fin(d+1)→HensonOneType 4 E at common level m, and a genuine later survivor tuple later:Fin d→HensonOneType 4 E at one level H>c. Assume old_{f(i)}≤later_i and c∉N(later_i) for every survivor i, where f=Fin.succAboveEmb j.

The coded old type has zero-based rank 0. The target level c≥m follows directly from true coding-fibre membership.

## Construction

Choose a private UNUSED auxiliary type dummy = zeroPad(old_j,H), valid because old_j.level=m≤c<H. It is not a selected diary branch; it is only a temporary argument to the existing constructor. Form

  laterFull = j.insertNth dummy later.

Mathlib's verified Fin.insertNth_apply_same and Fin.insertNth_apply_succAbove give

  laterFull_j = dummy
  laterFull_{f(i)} = later_i.

Thus laterFull has level H on every coordinate. For any non-code k≠j, Fin.exists_succAbove_eq supplies its unique index i∈Fin(d), so old_k≤laterFull_k and c∉N(laterFull_k) follow from the true survivor data.

Apply verified k4_construct_actual_precode_target_front (#470) to old,laterFull,x. It constructs a genuine pre-code target tuple pre at exactly c, whose coded coordinate is the TRUE target old-column type of the actual original c, with rank zero and two directed old columns. All old target types extend to pre, and pre remains injective. Its complete canonical age is genuine and below the old complete canonical age, with coded singleton age ONE.

Restrict the existing constructor's survivor conclusions along f and rewrite laterFull_{f(i)}=later_i: for EVERY real survivor i,

  pre_{f(i)}≤later_i,
  N(pre_{f(i)})=N(restrictPrefix(later_i,c+1)).

No dummy appears in the statement of this new theorem or later proof. Its entire output consists of the REAL code target prefix and REAL surviving target types, plus age consistency/bounds. This also gives the exact match required by physical survivor deletion (#475).

## Hostile audit

1. Only genuine real sourceCodingFibre membership of x supplies the code target old prefix at c. A hypothetical target word is insufficient.
2. Target K4 forbidden-family avoidance supplies safe K3-free neighbour data for the true target original; do not assume target rank zero without the old type rank and antitone extension.
3. The target cutoff H is STRICTLY beyond c; H=c does not provide the code bit at c.
4. The temporary dummy must reach H, but it is NEVER claimed to be in a future target coding fibre or a surviving diary branch.
5. All actually surviving later types live on Fin(d), not Fin(d+1). The map f=Fin.succAboveEmb j is the TRUE TARGET survivor order, not arbitrary relabelling.
6. Fin.insertNth j dummy later is used only to supply a logically irrelevant entry to the older constructor; no unproved theorem of tuple insertion is added.
7. For k≠j, existence of i with f(i)=k follows from the Mathlib Fin.exists_succAbove_eq theorem. No component outside the image of f is used.
8. Every later survivor extends the corresponding old target type with FULL positive and negative bits. Old neighbour inclusion alone is insufficient.
9. All later survivor types have zero TRUE TARGET bit at c; source old-bit zero is insufficient without actual induced-image proof (merged #433 supplies it).
10. No order-preserving assumption on the source→target embedding e; code cut is c=e(x.level).
11. True old target types must have one common level m and be pairwise distinct for the pre-code injectivity proof (#470).
12. If d=0, there are no survivors. The only old sort j is coded and the theorem remains valid without inventing a Fin(0) index.
13. The old full canonical age and true pre-code canonical age remain functions over ALL admissible supports on d+1 sorts, including code/mixed triples; no raw=canonical identity is asserted.
14. The output does not assert that pre-code full age equals the old full age. This is the task of the genuine survivor endpoint age sandwich (draft PR #488) after numeric endpoint equality from merged #482.
15. The temporary dummy is NOT used to compare ages of a fictitious final full front; the output has no dummy, unlike an earlier optional far-front construction.
16. This is only ordinary-L age geometry, not the full Kpt E/B3 event history, meet/split ordering, diary persistence, 24-count or big Ramsey lower bound.
17. Frozen black manuscript proof remains unchanged, and its global history-realization validation marker is not promoted.

## Lean gate

State a constructor returning only pre:Fin(d+1)→HensonOneType4 E with exact code-level, genuine code-column, injectivity, survivor-to-later extension and zero-bit prefix equality, genuine canonical pre-age, pre≤old full age and coded singleton one. Implement via checked #470 with Fin.insertNth (one internal dummy only). Exact-head Lake build, strict named standard-only axiom reports and full Lean CI before merge.
