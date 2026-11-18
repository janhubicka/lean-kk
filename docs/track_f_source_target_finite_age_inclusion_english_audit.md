# Track F — conditional source-to-target inclusion of complete finite clique classes

18 November 2026. English proof and hostile scope audit committed **before** Lean.

## Target

Fix genuine chronological source and target Henson edge relations \(E_s,E_t\), an injective *induced* graph embedding \(e\) (not necessarily chronological), and genuine target types \(v_i\) all at target level \(H\). Fix genuine source roots \(u_i\) at source level \(m\). Assume for **each** coordinate \(i\) that the set of **actual source coding nodes** whose images realize \(v_i\), namely \(\operatorname{sourceCodingFibre}(E_t,e,v_i)\), is recursively rank-large above \(u_i\) at the actual source rank.

Then **every** symmetric finite labelled graph \(B\) on \([0,N)\), whose every nonempty directed clique satisfies the *actual source raw support* inequality at \(u_i\), must satisfy the corresponding *actual target raw support* inequality at \(v_i\), for every nonempty directed clique of \(B\). Concretely, for each clique \(C\),
\[
 |C|\le\operatorname{RawAge}^{E_t}_{H}\bigl(\sigma[C];(v_i)_i\bigr).
\]

This is a full **finite-class inclusion** under explicit simultaneous individual fibre largeness, not a proof that compatible target types with all desired properties can be synchronized.

## Proof

1. By merged, exactly axiom-checked source finite richness [PR #367](https://github.com/janhubicka/lean-kk/pull/367), apply the source theorem to the chosen target coding fibres \(S_i=\operatorname{sourceCodingFibre}(E_t,e,v_i)\) and \(B\). This produces strictly increasing ACTUAL source originals \(f(0)<\cdots<f(N-1)\) with exact source columns, every prescribed edge and nonedge, and a genuine coding-node witness of \(f(a)\in S_{\sigma(a)}\).

2. Fix a directed clique \(C\subseteq[0,N)\) in \(B\). Let \(W=f[C]\), a genuine **source-original clique**. The increasing map \(f\) is injective on \([0,N)\), so \(|W|=|C|\), and its induced graph bits prove that \(W\) is a directed clique of \(E_s\).

3. The already verified physical target lower-bound theorem [PR #335](https://github.com/janhubicka/lean-kk/pull/335), \`trackFCommonRawAge_target_ge_sorted_source_clique\`, requires a TOTAL sort map on genuine source originals, rather than just a sort map on the abstract B indices. Construct one on the finite image \(W\) by setting \(\lambda(f(a))=\sigma(a)\). This is **well-defined by the injection** of \(f\); outside \(W\), choose an arbitrary dummy sort \(\sigma(0)\). In Lean, take the classical witness of \(a\) for each \(w\in W\) and prove independence of the witness using injectivity. No source/target chronological compatibility of \(e\) is used.

4. The fibre witness on each \(f(a)\) realizes \(v_{\sigma(a)}=v_{\lambda(f(a))}\). Every label occurring in \(W\) belongs to \(\sigma[C]\). Apply the verified physical theorem to \(W,\lambda,\sigma[C]\). Every image \(e[W]\) is a target directed clique strictly after target prefix \(H\) and joined in both directions to every vertex of its genuine old common-neighbour pool. Target \(K_\ell\)-avoidance forces
   \(|W|\le\operatorname{RawAge}_{H}^{E_t}(\sigma[C])\). Use \(|C|=|W|\).

All clique inequalities hold. This is exactly the raw feasibility condition for every finite B in the source class to remain feasible at the target front.

## Hostile audit and limits

- We **do not** assume an already-proved simultaneous target rank/profile synchronization; we assume explicitly *the actual individually compatible fibres* at the fixed levels. Simultaneously arranging such a family while preserving the source profile remains to be done.
- \(e\) is injected and induced, **not order-preserving**. The source originals \(f(a)\) are chosen increasing, but their target indices \(e(f(a))\) need only be beyond target level \(H\), as guaranteed by the fibre definition.
- The target common-neighbour pool is the true pool computed from \(E_t\), not an abstract diary profile.
- \(B\) may repeat any source sort an arbitrary number of times and may be empty. A total \(\lambda\) exists because the input sort map \(\sigma:\mathbb N\to\mathrm{Fin}(d)\) already exists, even when \(N=0\). Its values outside \(W\) have no effect.
- If \(C\) consists of just one vertex, the same physical clique theorem applies, with positive singleton target age. If \(C=\varnothing\), the claimed conclusion is restricted to nonempty supports; no spurious empty-support equation is introduced.
- Our target conclusion is **inclusion of finite feasible clique constraints**. It is not numerical equality of raw ages (redundant inequalities can have different values), nor an independent proof of canonicalization. A separate verified integer-profile canonicalization theorem can later promote finite-class equality once the reverse inclusion is established.
- The theorem must preserve BOTH directions of each actual edge and each old target column; using only positive adjacency would lose inducedness in K-free graphs.
- This does not establish any unavoidable diary orbit or exact BRD lower bound.
- The final Lean statement and all subsidiary declarations must build in exact-head CI and pass the strict standard-only axiom gate before being marked validated.

## Next dependency

The reverse inclusion (target-to-source) on finite feasibility is tied to the already verified nonempty-support numerical upper bound \`trackFCommonRawAge_target_le_source_of_large_fibres\` together with correct treatment of true old certificates. The **geometric existence** of simultaneous non-root compatible target fibres with a common target level and correct distinctness remains the central unverified part of the manuscript synchronization lemma.