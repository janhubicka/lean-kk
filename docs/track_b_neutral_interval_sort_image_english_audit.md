# Track B: finite neutral intervals and raw support-image transport
**15 November 2026. English proof and adversarial audit, committed before Lean.**

**20 November 2026 update:** the historical canonical-map gap recorded below
is now closed for support-monotone raw bounds, hence for every actual complete
old-column raw bound, even under noninjective sort maps. The
[arbitrary-map proof](track_b_canonical_sort_pullback_english_audit.md) and
[physical transport proof](track_b_physical_canonical_sort_transport_english_audit.md)
passed the completed [PR #414 integration gate](https://github.com/janhubicka/lean-kk/actions/runs/44781646067)
for head `4a275de622617da97a132ab8b8adf17cbb989c7b` (9,727 build jobs,
parser self-test, 955 exact standard-only reports). CI checked merge
`0792d8f297325eb5c80f807c2010a702789f77ac` over the newer main
`ddf60ae5ddba9fbc846dd3072dabc44fdc829ea5`: all 932 main names plus the
23 Track B names are retained. The five proof modules are unchanged from
the historical 953-report checkpoint `a433ad84f3881da535ee3e7164ff32e3337d2c3c`,
which remains a valid proof pin. The earlier 15 November text is preserved
below. Arbitrary nonmonotone raw tables still do not satisfy canonical
transport; selected-pivot coding and full parameter-closed Kpt source
synchronization remain separate obligations. No local full gate is claimed.

## Scope

PR #219 (merged as \`3967000199e4f580f9ebb4d4ded335875d00719f\`) establishes an exact one-original raw-age recurrence and the same-step conjunction of genuine \(K_\ell\)-free safety and all-support raw/canonical age neutrality. Here we derive (A) a **finite chronological interval** of actual safe, age-neutral insertions from certificates at every intervening original and (B) a correct raw old-column transport under an arbitrary map of future sorts. Neither manufactures the certificates or proves an infinite resolved-copy schedule.

### A. Finite chronological neutral interval

Fix an actual symmetric irreflexive original graph \(E\), \(\ell>0\), \(d\), a fixed typed future column \(c:\mathbb N\times d\to2\), an initial prefix \(b\), and a finite horizon \(m\). Assume the **actual original** \([0,b)\) is \(K_\ell\)-free. For every \(n\in[b,b+m)\), assume independently:

1. \(\operatorname{finiteNeighbourCliqueCheck}(E,n,\ell-1,x\mapsto E(x,n))=\mathrm{false}\), the complete actual old-neighbourhood safety certificate (including reserved, selected, split/coding, parameter, and gap originals).
2. For every admissible nonempty future support \(U\) on which the new original \(n\) has *all* positive typed future bits, write \(X_n(U)=\{p<n:\forall t\in U,c(p,t)=1\}\) and \(M_n(U)=\{x\in X_n(U):E(x,n)=E(n,x)=1\}\). Require
\[
1+\rho_E(M_n(U))\le\rho_E(X_n(U)).
\]

**Theorem:** \([0,b+m)\) remains \(K_\ell\)-free and, *pointwise over all nonempty supports*, both its raw finite-old-column function and integer-witness canonicalized age equal the corresponding functions at prefix \(b\).

**Proof:** Induction on \(m\). For \(m=0\), both statements are identities. At \(m+1\), restrict both quantified certificates to the earlier interval; obtain the induction hypotheses at \(b+m\). Apply the fully checked \`actual_original_stage_preserves_free_and_all_support_age\` to the *actual* original \(b+m\) and full typed column \(c\); it yields free prefix \(b+m+1\) and equality of both ages across this step. Compose equalities with the induction hypotheses. The arithmetic \(b+(m+1)=(b+m)+1\) is literal chronology, not a Kpt source-cut index or a selected-macrodiary rank.

**Corollary:** If the full old canonical age at \(b\) was some specified \(\mathsf{upper}\), then the final age at \(b+m\) is the *same* \(\mathsf{upper}\). This is the exact preservation interface needed for neutral stretches between distinct prescribed cover drops. **It says nothing about realizing one or more cover drops.**

### B. Reindexing supports correctly

Let \(e:\operatorname{Fin}(d')\to\operatorname{Fin}(d)\) be **any** map, including non-injective. For \(U'\subseteq\operatorname{Fin}(d')\), set \(e[U']\) to its finite image and pull the full column back by \(c'(p,t')=c(p,e(t'))\). Then
\[
 X_{U'}(P,c')=X_{e[U']}(P,c)
\]
literally as finite original sets. Membership: \(p\in P\) and \(\forall t'\in U', c(p,e(t'))=1\) is equivalent to \(p\in P\) and \(\forall t\in e[U'], c(p,t)=1\), by the defining image witness. In particular, if \(U'\) is nonempty of size at most \(\ell-1\), then its image remains nonempty and has cardinality at most \(\ell-1\). Thus the image defines an admissible support for the original \(d\) sorts.

It follows for **every** raw age:
\[
 B_{P,c\circ e}(U')=B_{P,c}(e[U']).
\]
The same exact identity holds at an enlarged actual original prefix \(P\cup\{v\}\). Thus taking old common-neighbours and adding a real original commutes with arbitrary support-image pullback **at the level of raw capacities**.

**Not proved:** canonical integer-graph-age transport under arbitrary \(e\). For non-injective \(e\), distinct sorts can become identified and alter the available normalized integer weight systems; on an injective inclusion, constraints involving deleted sorts can matter. Any application to splitting/coding must separately establish the precise admissible-weight and canonicalizer restriction maps (including all support constraints, not only the selected shadow).

### Adversarial checks

1. Prefix safety must be checked for *every* original \(n\), not only the chosen selected originals or gadget endpoints. Skipped original indices may still influence the fixed original graph, and fresh reserved block isolation does not imply the mixed later selected certificate.
2. The interval theorem assumes one fixed full typed column \(c\) and sort dimension \(d\). If the macrodiary changes the active sort set inside the interval, apply a separately verified sort-transport lemma first; do not reuse the interval theorem by silently identifying coordinates.
3. The raw-age neutrality budget must hold simultaneously on every admissible nonempty support positively seen by \(n\), rather than only the distinguished cover support \(T\).
4. Positive passing bits may be neutral; zero padding is a special case, not required.
5. The old pool \(X_n(U)\) is **all** original indices below \(n\), not just members of a reserved tag partition. Parameters and gaps which are actual original vertices are included.
6. Mixed cliques use two-sided adjacency for each new mutual neighbour; a one-sided directed link is insufficient.
7. The implication from a genuine \(K_\ell\)-free enlarged prefix to the raw-neutrality **converse** is established in PR #219; equality of canonical ages is still strictly weaker than equality of raw age functions.
8. A raw sort-image identity requires no injectivity. It may shrink support cardinality; the statement must use the image support, *not* the original support with a false pointwise identification.
9. A dimension-changing split/controlled coding is not merely original-vertex insertion. It can change support data before or after a neutral interval.
10. Even exact equality of raw old-column ages across an interval does not match Kpt auxiliary \(E\), full dependent old/upper \(L^+\) I1/I2/I3/(B3) cuts, physical Kpt source rank, or inverse-source labels. The K4 q2/cuts 10,22 obstruction survives.
11. Avoid the invalid "seed every Kpt prefix ancestor" shortcut: it makes every lower cut I1-interesting.
12. Finite iteration is *not* an infinite existence theorem. The induction takes as premises all safety and neutrality certificates for the proposed finite horizon; it constructs no special embedding \(\alpha_{\rm ub}\).

### Acceptance

English first, then independent Lean modules with only checked theorems as imports. Exact-head hosted full \`lake build\` and registered named standard-only transitive axiom reports must pass before adding manuscript green/blue markers for this work. Keep all 12 global bounded-copy/BRD assertions pending and frozen black text unchanged. Any manuscript overlay marks should be in the olive successor-tree block with correct source pins.
