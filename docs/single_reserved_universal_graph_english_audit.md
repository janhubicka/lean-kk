# One explicit reserved support block joined to the universal finite future

**13 November 2026 — English-first proof and adversarial audit.** This construction is the first step toward the complete graph-age gadget, extending the already hosted-verified universal finite future from PR #86 and raw support budget from PR #89. It is a **standalone ordinary-L finite graph**, not an assumed Henson/Kpt physical source.

## Setup

Fix \(\ell>0\), finite sort set \(\mathrm{Fin}(d)\), arbitrary raw graph-age bounds \(B:\mathrm{IntegerGraphSupport}(d,\ell)\to\mathbb N\), and one admissible nonempty support \(T\).

Let \(W_B\) be the literal finite dependent-sum future graph of PR #86, whose vertices are pairs \( (w, (j,t))\) with normalized weight \(w\) feasible for **all** support bounds \(B\), sort \(j\), and one of \(w_j\) individual slots. Edges within a given component index \(w\) are complete off-diagonal; between distinct indices they are absent in both directions. Every clique \(s\subseteq W_B\) has \(|s|<\ell\) and satisfies the bound \(|s_T|\le B(T)\).

Define \(r=\ell-1-B(T)\) using **truncated Nat subtraction**. Let \(R_T\) be a fresh complete clique on the finite set \(\mathrm{Fin}(r)\), disjoint by constructor tag from all future vertices. The augmented carrier is a sum type \(V_T=\mathrm{Fin}(r)\oplus \mathrm{UniversalWitnessVertex}(d,\ell)\); the designated finite graph vertex set is the entire left part together with only the **feasible** right vertices \(W_B\). Define ordinary Boolean \(L_T\) on this sum:

- between two reserved vertices q,q', put \(L_T(q,q')=1\) iff \(q\ne q'\);
- between two right vertices u,v, use the genuine universal-future edge of PR #86;
- across reserved q and future u, put **both directed bits** equal to decide(sort(u)∈T).

All other atoms are false, in particular the diagonal. The right ambient sum contains extra infeasible vertices which are **not** in the designated vertex set; the construction makes no claim about their clique age.

## Main claim

**Every** directed clique \(s\) inside the designated finite vertex set has cardinality strictly below \(\ell\). Thus the explicitly constructed labelled graph is \(K_\ell\)-free.

Proof splits into whether \(s\) has a reserved member.

1. If there is no reserved vertex, its vertices are all right vertices. Pulling them back by the injective right constructor gives a clique \(s_W\subseteq W_B\), and the already verified theorem makes \(|s|=|s_W|<\ell\).
2. If \(s\) contains a reserved q, all its future vertices must have sorts in T, since each is adjacent to q in both directions and the mixed bit was defined as decide(sort∈T). Again pull the future vertices back to \(s_W\subseteq W_B\), a directed clique. Thus \(|s_W|\le B(T)\) and \(|s_W|<\ell\). The reserved part of s has size at most r. By the verified sharp subtraction lemma from PR #89, \(r+|s_W|<\ell\). The two parts are disjoint by constructors and partition s exactly, so \(|s|\le r+|s_W|<\ell\).

This is a **literal graph construction and K-freeness proof**, not a conditional use of an unbuilt support column. The one-block support condition holds by the definition of the Boolean table.

## Sharp obstruction for an infeasible additional component

If an arbitrary normalized vector \(w\) violates B(T), i.e. \(w(T)>B(T)\), then \(w(T)\le\ell-1\) forces \(B(T)<\ell-1\), hence r>0. If one **adds** a complete component with precisely w_j vertices of each sort and the same support column, the entire reserved R_T together with its T-sorted vertices forms a clique of cardinality \(r+w(T)\ge\ell\); in particular it contains a forbidden \(K_\ell\). This is the sharp local obstruction, and is only a theorem of the **augmented** graph after the extra infeasible component has been attached. It is not a claim that the existing W_B includes such a component.

## Adversarial checks

1. **Two cases are essential:** without a reserved vertex a clique need not lie in support T. One cannot use \(B(T)\) to bound every future clique.
2. **Nat subtraction saturation:** when B(T)>ell−1 the reserved part is empty, so there is no reserved-vertex case. The verified budget lemma uses a *separate* future cardinality bound \(|s_W|<\ell\), not the false equation r+B(T)=ell−1.
3. **Component multiplicities:** a weight vector with two vertices of the same sort contributes two different future vertices. Only the Sigma slot construction preserves this.
4. **Both directed support bits:** a directed clique checks every ordered edge, so the graph table must be symmetric across the sum constructor boundary.
5. **Right ambient carrier versus designated W_B:** the full dependent-sum type also includes vertices indexed by infeasible w. All clique tests must restrict to the actual designated finite vertex set.
6. **No cross-component edges:** without this rule the future part of an augmented clique could mix multiple weights and exceed raw bounds.
7. **No unwanted old graph:** the construction has one reserved Q_T and future W_B only; it does not yet adjoin arbitrary old P or gap G with prescribed columns.
8. **No all-support claim:** this construction enforces the raw bound at just one T. The full universal gadget has one reserved block per support, with zero edges among distinct blocks.
9. **\(\ell=1\):** support type is empty; the theorem is vacuous in T. \(\ell=0\): the strict-K_0-free conclusion is false. Keep ell>0.
10. **No relative existence theorem:** even though this standalone graph is finite and K-free, attaching it over a fixed prior Henson prefix with all old L and Kpt auxiliary E records is another problem.
11. **No common orbit inference:** finite ordinary-L realizability does not imply identical complete upper L+ successor types assigned to each parameter-closed source node or a labelled monoid inverse source.
12. **Exact PR dependencies:** refer to the actual verified \`universalWitnessFuture_clique_card_lt\`, \`universalWitnessFuture_clique_respects_raw\`, \`rawSupportBlock_add_clique_below\` and \`universalWitnessEdge\`; do not replace them with unproved abstractions.

## Lean work plan

Use a finite vertex subtype inside a tagged sum, not an unstructured union on Nat. Prove constructor injection, a strict partition of any candidate clique into the reserved and future parts, exact transferred future-clique membership, and the support restriction when a reserved member exists. Apply the verified cardinal inequality. Then generalize to all support blocks by a one-reserved-block clique-classification induction.

Do not mark any manuscript global theorem green until the explicit source embeddings, complete \(H^+\) parameter-closure and labelled inverse-source orbit are established.
