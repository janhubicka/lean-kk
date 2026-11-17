# Track B — exact chronological count of critical original insertions
**16 November 2026. English proof and adversarial checks committed before Lean source.**

## Statement
Fix one directed original graph E, one unchanged typed future column \(c:\mathbb N\times\mathrm{Fin}(d)\to\{0,1\}\), an admissible nonempty support U, a cut b and finite length m. Let

\[
X_n(U)=\{p<n:\forall t\in U,\ c(p,t)=1\},\qquad
M_n(U)=\{p\in X_n(U):E(p,n)=E(n,p)=1\}.
\]

Define the *criticality* indicator \(e_n(U)\) to equal 1 precisely if both (a) the new original n is positive to every sort of U and (b) \(\operatorname{cap}_E(M_n(U))=\operatorname{cap}_E(X_n(U))\); else 0. The counted number of critical original events is
\(C_{b,m}(U)=\sum_{b\le n<b+m}e_n(U)\).

The exact one-original lemma from the separately proposed Track B critical-source proof shows
\[
\operatorname{cap}_E(X_{n+1}(U))
 =\operatorname{cap}_E(X_n(U))+e_n(U).
\]
Induction on m therefore yields the *telescope*
\[
\operatorname{cap}_E(X_{b+m}(U))
=\operatorname{cap}_E(X_b(U))+C_{b,m}(U).
\]
The literal old-column raw bound at U satisfies
\[
B_{b+m}(U)=B_b(U)\mathbin{\dot-}C_{b,m}(U),
\]
where \(\dot-\) denotes natural truncated subtraction. This last formula uses
\((\ell-1-a)\dot- C=\ell-1\dot-(a+C)\), true for all naturals.

## Finite induction in detail
At m=0 the original prefix and the count are unchanged. For m+1, decompose the actual finite prefix \([0,b+m+1)\) as \([0,b+m)\cup\{b+m\}\). The exact original insertion age formula gives
\[
B_{b+m+1}(U)=B_{b+m}(U)\dot-e_{b+m}(U).
\]
By definition \(C_{b,m+1}=C_{b,m}+e_{b+m}\).
Apply the induction hypothesis and associativity of truncated subtraction:
\[
(B_b\dot-C_{b,m})\dot-e_{b+m}
  = B_b\dot-(C_{b,m}+e_{b+m}).
\]
No original graph symmetry or forbidden-clique-freeness assumption is needed to get the raw formula; mutual directed edges are essential for the capacity recurrence. The actual base enumeration includes every original gap, reserved, selected, and split/coding-parameter vertex; this is NOT a selected-subsequence identity.

## Stronger consequence under actual K_ell-freeness
If the *entire* final original prefix is K_ell-free, every intermediate original-prefix graph is as well. The exact old clique capacities never reach ell and no raw-support decrease is hidden by saturation. In particular, \(C_{b,m}(U)\le B_b(U)\), and
\[
B_b(U)-B_{b+m}(U)=C_{b,m}(U).
\]
This identifies the exact number of actual critical original insertions **per support**, but it does not identify a canonical-graph-age-cover count or a full diary interesting-level count: canonicalization has global integer-witness constraints, and Kpt auxiliary E/meet-parameter events may happen without raw changes.

## Adversarial limits
1. *Fixed sort dimension/column:* splits, controlled coding and sort-relabelings must first be transported; no naturality of canonicalizers across dimensions is assumed.
2. *True original chronology:* count every actual original, not only chosen selected tops. A skipped gap can be critical if its true future columns are positive.
3. *Full support:* positivity is \(\forall t\in U\), not a single distinguished coordinate.
4. *True clique capacities:* the criticality test is about an old maximum mutually adjacent directed clique, not the number of linked vertices.
5. *No saturated iff without safety:* raw decrease can stop at zero even if an old clique capacity keeps increasing.
6. *Multiple supports:* one physical new original can be critical at many U, not necessarily a unique graph-age-poset cover.
7. *Not the upper BRD theorem:* no unbounded safe schedule is generated; complete dependent Kpt old/upper \(L^+\) records, auxiliary q2, B3-loss/relative-continuation, and labelled inverse-source orbit remain separate.

## Validation contract
Use the English proof before Lean. New module must import the exact per-original criticality theorem from the consolidated Track B PR #253. Require a new standalone exact-head hosted build and named standard-only transitive axiom reports with no \`sorryAx\`; do not add manuscript GREEN markers or promote global bounded-copy/BRD claims while pending.
