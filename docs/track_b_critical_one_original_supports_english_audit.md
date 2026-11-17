# Track B: exact one-original critical-support jump dichotomy
**15 November 2026. English mathematics and adversarial audit BEFORE Lean.**

## The exact refinement

The already kernel-checked full original insertion formula of [PR #219](https://github.com/janhubicka/lean-kk/pull/219) computes
\[
 \rho(X\cup\{v\})=\max\{\rho(X),1+\rho(M_E(X,v))\},
 \quad M_E(X,v)=\{x\in X:E(x,v)=E(v,x)=1\},
\]
for a genuinely new original \(v\notin X\), using complete directed cliques. Since \(M_E(X,v)\subseteq X\), monotonicity gives \(m:=\rho(M_E(X,v))\le a:=\rho(X)\). There are **only two possible capacity transitions**:
\[
 \rho(X\cup\{v\})=
 \begin{cases}
 a+1,&m=a,\\
 a,&m<a.
 \end{cases}
\]
The equality case means the new original is mutually adjacent to *some maximum old clique*, NOT to every old common neighbour and NOT merely to a maximum cardinality set of selected branches. When \(m<a\), adding the original is capacity-neutral despite positive passing bits.

For a fixed future-sort support \(U\), let \(X_U(P,c)\) be *all* prior original vertices positive to every sort in \(U\). Define \(\mathrm{Critical}(U,v)\) by
\[
 \bigl(\forall t\in U,\ c(v,t)=1\bigr)
 \quad\text{and}\quad
 \rho_E(M_E(X_U(P,c),v))=\rho_E(X_U(P,c)).
\]
Then the **literal raw support bound** is exactly
\[
B_{P\cup\{v\}}(U)=
 \begin{cases}
 B_P(U)-1,&\mathrm{Critical}(U,v),\\
 B_P(U),&\text{otherwise},
 \end{cases}
\]
with the natural/truncated subtraction convention. Thus every single original insertion changes **each raw support by at most one**, without an isolated clique-block assumption. A critical support may nevertheless have *no visible raw drop* if the old raw value was already zero because \(\rho_E(X_U)\ge\ell-1\). This clipping is unavoidable in abstract directed tables.

If the **entire new original pool** \(P\cup\{v\}\) is \(K_\ell\)-free, then \(\rho_E(X_U\cup\{v\})<\ell\); in the critical case this yields \(B_P(U)\ge1\). Consequently a **strict raw drop by exactly one** occurs *if and only if* \(\mathrm{Critical}(U,v)\). This is the sharp physical per-original criterion for a non-neutral raw age event. It is NOT a claim that the **canonical integer graph age** drops by one at precisely those supports: canonicalization can propagate or mask changes through the global normalized witness constraints.

## Impact on the proposed resolved-copy induction

The natural stage certificate becomes: for each actual new original \(v\), (1) the complete old-neighbourhood \(K_{\ell-1}\)-free test (physical safety), (2) the full set \(\mathscr C(v)\) of critical supports, determined from the *actual* old graph and all future columns (raw age change), and (3) an independent proof that canonicalization of that new raw function gives precisely the prescribed macrodiary cover or neutral event. Earlier cardinal-only reserved block budgets are sufficient tests in special cases, not the intrinsic general update.

In particular, one original may be critical for **many** supports simultaneously. For instance take a single positive original in a previously empty old pool with at least two future sorts. Every nonempty admissible support it sees is critical, and the raw bound drops at each. A one-original insertion is therefore *not automatically a cover in the canonical graph-age poset*. The missing schedule theorem must still choose the originals so that its *canonical* age follows the desired cover chain.

## Adversarial checks

1. Freshness v outside X is required for the exact max recurrence; without it an artificial extra clique is counted.
2. Mutual edges in both directions are required, not a selected-shadow or one-directional link.
3. The criticality test uses **clique capacity**, not cardinality of the linked set.
4. The "gain at most one" argument is pure finite-graph arithmetic and does not require K_ell-free safety.
5. The strict raw-drop iff criticality requires genuine K_ell-freeness of the **enlarged original pool** to exclude saturation.
6. The raw decrement is a natural-number subtraction; for an already zero bound it is still zero even if the underlying capacity grows.
7. A positive type column does not imply a critical support: the new original may fail to see any *maximum old* clique.
8. Conversely a critical support has a positive column at every sort in the whole U, not merely one selected sort.
9. Off-support raw bounds remain unchanged, regardless of old original-to-original edges.
10. Critical supports can occur on several incomparable/smaller supports at once, so a single physical original is not inherently an age-poset cover.
11. Equality of raw ages is stronger than equality of their canonicalizations; no converse via canonical ages is used.
12. Full L+ auxiliary E, terminal/parameter closure, K4 q2 cuts 10/22, source-rank transport, and labelled inverse-source orbit remain independent.
13. These are finite stage diagnostics, not a coherent unbounded schedule or BRD classification.

**Verification policy:** formalize named pure and conditional statements separately; require exact-head full Lean build and transitive axiom audit. Do not mark global bounded-copy or BRD assertions green, and preserve frozen black manuscript prose.
