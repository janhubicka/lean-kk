# Raw support bounds give an exact safe budget for one reserved block

**12 November 2026 — English proof and adversarial audit before Lean.** This is a finite ordinary-L statement, not an assumption about full numerical-H/parameter-closed corrected B3.

## The sharp arithmetic budget

Fix \(\ell>0\), an arbitrary raw bound value \(b\in\mathbb N\), and \(n\le b\) with \(n<\ell\). Put
\[
 a=(\ell-1)-b
\]
where subtraction is truncated in \(\mathbb N\). Then
\[
 \boxed{\quad a+n<\ell.\quad}
\]
Proof by two exhaustive cases. If \(b\le\ell-1\), then \(a+b=\ell-1\) and \(a+n\le\ell-1\). If \(b>\ell-1\), then \(a=0\), and \(a+n=n<\ell\). Both inequalities \(n\le b\) and \(n<\ell\) are genuinely required; dropping the latter fails when \(a=0\). In the common forbidden-clique context, the \(n<\ell\) premise follows from a separate old-plus-future K_\ell-free check. In particular, \(\ell=1\) is covered by the formula only with \(n=0\); no false nonempty graph is inferred.

## Universal future budget (concrete ordinary L graph)

Let \(B:\operatorname{IntegerGraphSupport}(d,\ell)\to\mathbb N\), \(T\) an admissible support, and \(W_B\) the actual universal finite future from merged PR #86. Its verified theorem \`universalWitnessFuture_clique_respects_raw\` proves for *every* directed clique \(s\subseteq W_B\) that
\[
 n:=\left|\{v\in s:\mathrm{sort}(v)\in T\}\right|\le B(T).
\]
Its verified theorem \`universalWitnessFuture_clique_card_lt\` proves \(|s|<\ell\), hence \(n<\ell\). Substituting these into the sharp arithmetic lemma gives
\[
 \boxed{((\ell-1)-B(T))+
        \left|\{v\in s:\mathrm{sort}(v)\in T\}\right|<\ell.}
\]
This is a universal budget over *all* future cliques of the **one specifically constructed W_B**. It is not a theorem about an arbitrary fixed W.

## Actual four-pool relative certificate

The verified \`finitePoolCliqueCheck_gluing_all_support_witnesses\` theorem (merged PR #79) concerns the **actual** directed Boolean edge table E on natural-indexed vertices and four finite pools: old P, reserved Q, gaps G and future W, with a sort map into Fin d.

Fix B, T and set \(a=(\ell-1)-B(T)\). Suppose:

- the **actual** Q clique capacity is exactly \(a\);
- the old-to-reserved and gap-to-future E bits are zero, and Q is disjoint from the supported part of W;
- both directions E(q,w), E(w,q) of every Q–W bit are **exactly** decide(sort(w)∈T);
- the entire past \((P\cup Q)\cup G\) and the old-plus-future \(P\cup W\) are K_\ell-free;
- every directed clique \(s\subseteq W\) obeys the raw B(T) support-count bound.

Then \(((P\cup Q)\cup G)\cup W\) is K_\ell-free. Indeed, any such s is also K_\ell-free by heredity from the old-plus-future test, so n<ell. The arithmetic budget gives \(a+n<\ell\), precisely the universal right conjunct of the checked four-pool gluing iff. The old-plus-future test supplies the other conjunct. No false assumption that W_T itself is a clique and no cardinality-of-W_T shortcut.

This is a **relative certificate**: it is a valid implication for any E with the listed real columns and true clique tests. Unlike the earlier abstract universal W_B statement, it uses the genuine Nat-indexed L table, but it does NOT build such E, Q and W. The physical one-point left-density theorem PR #87 can realize each *individually certified* new original with a full old column. A future induction must construct the whole support-block/future witness schedule while verifying the premises simultaneously.

## Adversarial audit

1. **Natural subtraction saturation:** for B(T)≥ell−1 the intended reserved block is empty. The equation \(a+B(T)=\ell-1\) is false when B(T)>ell−1. The proof splits cases and instead uses n<ell in the empty-block case.
2. **Need actual future K_\ell-freeness:** \(n\le B(T)\) alone cannot give \(n<\ell\) if B(T) is very large. The old-plus-future hypothesis supplies this, and is never silently omitted.
3. **Need past K_\ell-freeness:** a forbidden clique contained wholly in P∪Q∪G is not visible to a support budget.
4. **Need full old-plus-future test:** a forbidden clique in P∪W can avoid Q completely.
5. **Reserve capacity, not reserve cardinality:** the physical numerical-H prefix may have many real copies; its capacity is the relevant value. The theorem assumes the verified **exact** capacity of Q, not its vertex count.
6. **W_T may be non-complete:** raw B controls maximum counts within arbitrary clique subsets of W. Never replace capacity by |W_T|.
7. **Both directed Q–W bits:** the generic gluing iff works in a directed Boolean language and requires both orientations of each support bit.
8. **No unproved separation:** nonedges P–Q, G–W and Q∩W_T=∅ are explicit hypotheses. They are not consequences of a canonical graph-age equality.
9. **Repeated sorts:** count the actual vertices of s whose sorts lie in T; the support set T alone cannot encode their multiplicity.
10. **Zero and one threshold:** at ell=1, the old/future no-K_1 hypotheses force all relevant pools empty. The arithmetic lemma remains correct where its premises hold.
11. **Universal W_B vs physical W:** matching abstract support counts does not build a coordinate-preserving injection of W_B into a fixed Henson prefix. The finite four-pool theorem is conditional on having the concrete table E and its certificates.
12. **Parameter closure:** this ordinary-L budget does not discharge Kpt auxiliary E and the full corrected (B3) age-test source equivalence, the assigned complete L+ successor per labelled node, or the common inverse-source orbit.

## Formalisation plan

1. Prove the universal Nat inequality \(n\le b\), \(n<\ell\) ⇒ \((\ell-1-b)+n<\ell\) using \`omega\`, without a false cancellation.
2. Apply it to every clique in the **actual** finite universal future \`universalWitnessFuture\` using the verified no-K_\ell and full-support-bound lemmas.
3. Apply the already-verified four-pool gluing iff to any actual Nat-indexed E, P, Q, G, W under all existing hypotheses, with the exact Q capacity and the future clique support bound.

Require a full hosted \`lake build\` and strict standard-only named transitive-axiom reports for all three theorems. No manuscript green marker for physical source realization or full B3 is authorized by this calculation.
