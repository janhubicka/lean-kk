# Track F — physical raw-age transfer from arbitrary source types to private rank-zero daughters

18 November 2026. English proof and adversarial audit **before** Lean. The source is the actual chronological Henson graph \(E\), not a formal diary age. Let \(u_a\), \(a\in\mathrm{Fin}(p)\), be genuine one-types at the same original level \(m\); let \(S_a\) be rank-\(\operatorname{rank}(u_a)\)-large sets of actual coding nodes. Let \(\pi:\mathrm{Fin}(d)\to\mathrm{Fin}(p)\) be **arbitrary**, possibly highly noninjective, representing private requests for vertices of a desired finite graph.

## Statement

There are a common later level \(H\) and genuine rank-zero descendants \(g_i\) of \(u_{\pi(i)}\), with each \(S_{\pi(i)}\) still rank-zero large above \(g_i\), such that

1. For **every support** \(Q\subseteq\mathrm{Fin}(d)\) with \(|Q|\ge2\),
   \[
   \operatorname{RawAge}_{H}(Q;(g_i)_{i<d})
   =\operatorname{RawAge}_{m}(\pi[Q];(u_a)_{a<p}).
   \]
2. For **every private index** \(i\), \(\operatorname{RawAge}_{H}(\{i\};g_i)\ge1\).

All raw ages are \( \ell-1-\omega_E(\bigcap_{i\in Q}N(g_i))\), with the common-neighbour intersection taken over the full genuine initial segment. Equality is claimed for raw ages, **not** canonically normalized integer ages.

## Proof

Apply the verified private common-front theorem of PR #358 to the indexed family \(u_{\pi(i)}, S_{\pi(i)}\). It supplies \(H,g_i\) with \(g_i\ge u_{\pi(i)}\), rank zero and fibre largeness, and pairwise disjoint fresh marker sets \(V_i=N(g_i)\setminus N(u_{\pi(i)})\).

The *complete prefix* extension condition, not mere inclusion of old positive neighbours, gives \(N(u_{\pi(i)})\subseteq N(g_i)\) and implies that every fresh marker in \(V_i\) is at least \(m\). Its other end is strictly less than \(H\), because \(g_i\) is a genuine type at level \(H\). Therefore
\(N(g_i)=N(u_{\pi(i)})\cup V_i\)
with old vertices below \(m\), fresh vertices in \([m,H)\), and \(V_i\cap V_j=\varnothing\) for \(i\ne j\).

For \(|Q|\ge2\), apply the already verified physical disjoint-marker collapse theorem to identify the complete raw common-neighbour age at the later front with the original raw common-neighbour age of \(\pi[Q]\). This remains true if two distinct private indices share the same parent; the theorem imposes no injectivity on \(\pi\).

For singleton \(Q=\{i\}\), the genuine type safety condition says \(N(g_i)\) contains no directed \((\ell-1)\)-clique. The verified finite clique-check equivalence gives \(\omega_E(N(g_i))<\ell-1\). Hence the literal natural-number raw age \(\ell-1-\omega_E(N(g_i))\ge1\). There is no rank-saturation shortcut or extra assumption of positive singleton age.

## Adversarial audit

- **Original ranks may differ**, and \(\pi\) need not be injective. No uniform-rank fan construction is needed.
- **The same fibre can be requested repeatedly.** The verified private selection separates new positive markers, not original neighbourhoods.
- **An initially rank-zero parent can have an empty fresh set.** Its repeated indices remain valid, but any edge clique with both indices must satisfy the original singleton raw bound 1; this correctly prohibits an impossible edge.
- **Support sizes are counted *before* applying \(\pi\).** A two-private-sort support can collapse to a single original sort. The disjoint-marker equality still holds; incorrectly testing \(|\pi[Q]|\ge2\) would lose that case.
- **Canonical numeric ages are not transported.** Their values can change because singleton ranks shrink. We transport only genuine raw clique inequalities.
- **No actual B vertices are yet chosen.** This is the exact geometric capacity bridge; the next theorem must combine it with PR #355 and show induced chronology and original old-column preservation.
- **Empty index family:** both support statements are vacuous. The final graph realization may use \(d=N+1\) to avoid a total label map into \(\mathrm{Fin}(0)\).
- **Explicit hypotheses:** we require genuine source Henson one-types, actual coding-set largeness and a common original prefix. We do NOT assume diary persistence, target-side compatibility or any big Ramsey lower bound.

## Acceptance

Lean must prove the exact physical equality for arbitrary \(\pi\), arbitrary supports of size \(\ge2\), and singleton positivity using only standard axioms. The formal source-richness theorem for arbitrary finite labelled \(B\) is then a separate composition step. Frozen black manuscript text and global BRD validation marks remain unchanged.