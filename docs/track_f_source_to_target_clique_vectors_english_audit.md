# Track F — every source-feasible clique vector is target-feasible

18 November 2026. English proof **before** Lean implementation. This bridges merged full arbitrary-rank actual source richness PR #367 and merged physical future target clique obstruction PR #335.

## Hypotheses and precise conclusion

Fix genuine source and target \(K_\ell\)-free graph edge tables \(E_s,E_t\), with explicit normalized target forbidden-family avoidance (\(\ell\ge2\)). Let \(e:\mathbb N\to\mathbb N\) be **injective and induced on off-diagonal ordered pairs**, not necessarily order-preserving.

Fix a finite family of actual source one-types \(u_i\) over one source prefix \(m\), and actual target one-types \(v_i\) over one target prefix \(H\); the target types may coincide. Let
\(S_i=\operatorname{sourceCodingFibre}(E_t,e,v_i)\), consisting **only** of actual original source coding types \(t\) whose target images are after \(H\) and have both exact old \(v_i\) columns. Assume \(S_i\) is recursively large at the actual source rank of \(u_i\). There is no target rank matching hypothesis.

Fix any \(N\) and private-or-repeated sort labels \(\sigma:\mathbb N\to\mathrm{Fin}(d)\) on \([0,N)\). Assume the chosen abstract labelled **complete clique** is source-feasible:
\[
 \forall \varnothing\ne T\subseteq [0,N),\quad
 |T|\le R_s(\sigma[T]),
\]
where \(R_s\) is the raw age from the actual old source common-neighbour pools.

Then the same vector is target-feasible, i.e. for **every nonempty** target support \(J\subseteq\mathrm{Fin}(d)\),
\[
 \big|\{i<N:\sigma(i)\in J\}\big|\ \le\ R_t(J).
\]
The conclusion is a system of clique-vector inequalities, **not** numerical equality of raw ages.

## English proof

Let \(B(i,j)\) be true exactly when \(i\ne j\). This is a symmetric complete simple graph on the abstract finite interval \([0,N)\). Every nonempty subset \(T\subseteq[0,N)\) is a directed clique in \(B\), and the source-feasibility assumption gives all hypotheses of the newly merged **actual finite source richness** theorem #367. Apply it to the genuine fibre family \(S_i\), whose members are actual coding types by definition. Obtain a strictly increasing source original-index map \(f:[0,N)\to\mathbb N\), a fully directed **source clique** \(f[[0,N)]\), and for each \(i<N\) a genuine coding type \(t_i\in S_{\sigma(i)}\) with \(t_i.level=f(i)\).

Fix an arbitrary nonempty target support \(J\). Let
\[
 T_J=\{i<N:\sigma(i)\in J\},\qquad C_J=f[T_J].
\]
Strict increase of \(f\) makes it injective on \([0,N)\), so \(|C_J|=|T_J|\). The source full induced-graph theorem ensures that \(C_J\) is an actual source clique in **both** directions. For each \(c\in C_J\), there is a *unique* \(i\in T_J\) with \(c=f(i)\), and we assign to this actual original the sort \(\sigma(i)\in J\). Its actual coding witness belongs to \(S_{\sigma(i)}\), hence to the target fibre of \(v_{\sigma(i)}\) exactly.

Apply the merged physical source-clique-to-target-raw-age theorem #335 to \(C_J\) with this sort assignment. Injective induced \(e\) maps it to a genuine target clique entirely after \(H\), joined in both directions to the target common old neighbour pool \(Q_J\). Since \(E_t\) avoids \(K_\ell\),
\[
 |T_J|=|C_J|\le \ell-1-\omega_{E_t}(Q_J)=R_t(J).
\]
As \(J\) was arbitrary, the entire clique vector is target-feasible.

## Checks against circularity and extra hypotheses

1. The source clique is **constructed by #367**, not assumed as in #335.
2. The source fibres \(S_i\) are actual coding types, not the full tree of hypothetical safe finite types.
3. The target image map \(e\) is induced and injective, but **NOT** order preserving; its images may be in any order. The target-fibre definition itself ensures their indices are after the target prefix.
4. The source and target root families each have a common prefix level; those two levels need **not** agree.
5. The source and target one-types have no assumed equal rank here. Rank-large is used on the SOURCE roots only.
6. Repeated source or target sorts are allowed. The unique index inversion is needed only for the selected finite chronological injection \(f\).
7. A target support \(J\) may not be hit by any chosen vertex. Then the inequality has left side zero and is automatic, although the proof still treats it uniformly.
8. The empty selected graph \(N=0\) is harmless, since the sort map \(\sigma\) remains total.
9. Real complete B is chosen explicitly. Source feasibility of the TOTAL set alone is insufficient: the assumption covers **every nonempty subset**.
10. Both directed edge columns are preserved in source f and by e; do not use a one-sided graph assumption.
11. The actual target graph's normalized \(K_\ell\)-avoidance is explicit; avoiding \(K_\ell\) is not inferred from fibre largeness alone.
12. This proves inclusion of **feasible labelled clique vectors**. It does not imply equality of redundant raw mixed capacities, nor by itself synchronize targets, make them distinct, prove diary unavoidability or an exact BRD.

## Next possible composition

The previously verified upper bound #332 gives \(R_t(J)\le R_s(J)\) for each nonempty support, provided all old positive source neighbour images lie before \(H\) and every source fibre is large. This gives the reverse inclusion of target-feasible vectors into source-feasible vectors. Together with this new lower/vector inclusion, the two canonical finite sorted graph classes coincide **under those explicit synchronized family assumptions**. It remains a separate task to construct such a finite family of compatible pairs at common source and target fronts, with distinct target sorts and preserved source profile. No source/target compatibility or diary theorem is imported as an axiom.
