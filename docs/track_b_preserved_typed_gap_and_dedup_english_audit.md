# Track B — preserve typed columns across a certified neutral physical gap
**17 November 2026. English proof and adversarial analysis written before Lean source.**

## Audit and simplification of existing proof

The construction \`oldColumnZeroTail b c\` in \`Kk/ZeroTailPhysicalCoverSpacing.lean\` is *definitionally the same function* as the earlier \`delayedOldColumn b c\` in \`Kk/CofinalNeutralOldColumnAge.lean\`: both are \`c p t\` for \`p<b\`, and false for \`p>=b\`. Moreover the older \`delayedOldCommonNeighbourPool_eq\`, \`delayedOldRawBound_eq\` and \`delayedOldCanonicalAge_eq\` are precisely the finite common-pool, complete raw-age and canonical-age results that the later zero-tail file reproves.

We can therefore keep the published Track B names as **compatibility wrappers** and define \`oldColumnZeroTail\` as a reducible abbreviation of \`delayedOldColumn\`. This removes duplicate original combinatorics without removing any of the seven registered theorem endpoints, changing hypotheses, or promoting a global diary statement. Independently check the complete exact-head Lean build and named-axiom inventory after the refactor.

## Mathematical bridge — the second stage after real existing vertices, no zero-tail reset

Fix one normalized left-dense \(K_\ell\)-free Henson original graph \(E\), \(\ell\ge2\), a **fixed** positive finite sort dimension \(d\), an original prefix cut \(b\), and a complete typed future column \(c(p,t)\). Suppose a **first physical** support-\(T_0\) stage has already been constructed with a real reserved clique \(Q_0\subseteq[b,F_0)\), its entire gap-inclusive column
\[
 c_1=\operatorname{supportBlockGappedColumn}(b,Q_0,T_0,c),
\]
its full pointwise resulting canonical age \(G_{B_{[0,F_0),c_1}}=\mathrm{middle}\), and a genuine finite uniform positive-support stage \`HasUniformPositiveSupportStage\` in the *same* \(E\).

Choose any natural number \(m\) and put \(N=F_0+m\). Let \(W_0\) be **any finite set of actual original indices** already below \(N\); a future recursive construction may instantiate it as the true original image of the first stage's chosen finite top witnesses, but this is **not** inferred merely from the finite stage's existence. Require for every admissible nonempty sort support \(U\) that
\[
 \operatorname{originalCriticalCount}(E,\ell,d,F_0,c_1,U,m)=0.
 \tag{*}
\]
This hypothesis concerns the **unmodified complete column \(c_1\)**, including any positive bits on intervening vertices; it is not a zero-tail substitution. The verified exact critical-count telescope gives the *whole* old raw-age and therefore canonical-age identity
\[
  G_{B_{[0,N),c_1}}=\mathrm{middle}.
\]
Apply the already verified physical one-stage Henson canonical-cover theorem at the **actual later cut \(N\)** to the second cover \(\mathrm{lower}\lessdot\mathrm{middle}\). It yields a real \(Q_1\subseteq[N,F_1)\), \(|Q_1|=r_1\), a complete updated column \(c_2=\operatorname{supportBlockGappedColumn}(N,Q_1,T_1,c_1)\), \(G_{B_{[0,F_1),c_2}}=\mathrm{lower}\), a true finite second uniform positive-support stage and all physical negative old-to-\(Q_1\) edges.

In particular **every \(w\in W_0\)** is earlier than every member of \(Q_1\), and both directed original edge bits between \(w\) and \(Q_1\) are false. Moreover, because \(Q_1\) lies above \(N\), the complete **typed future column on every original \(p<N\)** is *unchanged*: \(c_2(p,t)=c_1(p,t)\) for every sort \(t\). This includes \(W_0\). The first stage's original \(E\)-based finite witness is still valid with its *own* original column and original first-stage parameters; no original graph bit is modified.

This is a finite **conditional** bridge. It does **not** generate (*), construct a coherent infinite resolved copy, show that all first-stage top witnesses can be chosen in an interval satisfying (*), transport evolving sort dimensions, synchronize the auxiliary \(Kpt\) old/upper dependent \(L^+\)/\(E\) source or establish common labelled inverse-source orbits.

## Ten adversarial checks

1. The earlier zero-tail and delayed-old definitions are literally equal *for all p and t*, not only for admissible supports. Their age theorem depends on nonempty supports, as before.
2. Keep each existing \`oldColumnZeroTail\`/pool/raw/canonical theorem name and its strict transitive-axiom report; wrappers must not silently delete a public theorem.
3. In the new bridge, the interval is \([F_0,F_0+m)\) in **actual original indices**. The full \`Finset.range N\` includes all unselected gaps and parameters.
4. Use the **same unmodified \(c_1\)** to evaluate (*), the next-stage prior age, and the second physical cover. A zero-tail rewrite would invalidate the witness-preservation claim.
5. \`W_0\` must consist of actual original indices below \(N\), not abstract tagged indices, generation coordinates, or chosen source names. The theorem itself does not identify \`W_0\` with the first stage's true \(f_0(W)\).
6. The unchanged-column identity is a literal equality for **all** old \(p<N\) and all sorts; it is stronger than an equality of canonical ages, but only concerns the old-to-*future* recipe.
7. The first finite \`HasUniformPositiveSupportStage\` is retained because its \(E\), first cutoff, column, support and reserved block are unmodified. This does not claim its selected future is compatible with the new second stage.
8. The entire second original reserved block is negative to **every** earlier original \(p<N\), hence to \(Q_0\) and \(W_0\), both directions; this is actual Henson adjacency, not an ideal raw-age operation.
9. (*), zero *raw* critical counts, is sufficient but not necessary for unchanged **canonical** age. A feasible diary argument might prove a weaker canonical no-change certificate instead; do not incorrectly treat (*) as a necessary condition.
10. If an intended positive witness is critical on some support, (*) is false. The result cannot be used to declare the global recursive schedule validated; every further stage needs a generated or independently certified age invariant and all auxiliary source synchronization.

## Manuscript boundary

If this branch passes full Lean checks, only the exact finite wrapper and conditional physical bridge receive their narrow GREEN/BLUE source annotations. Keep \`Lem:Kk_Resolved_Copy\`, its full (I1)–(I3)/(B3) condition and the final BRD upper/lower bounds PENDING. Frozen black prose is not edited; if it asserts a global schedule from finite cover composition, attach a TODO to the precise inference. The old circulation-cleanup TODO about an abandoned recurrence should not be reintroduced merely to describe this new bridge.


## Further adversarial finding: the real witness-preserving interface needs a NEW continuation column

The first draft bridge accepted only \`c_1=\mathrm{supportBlockGappedColumn}(b,Q_0,T_0,c)\` through the entire later interval. This is **too weak for the intended application**: by definition, \`c_1(p,t)=0\` for every \`p\ge F_0\` because \`Q_0\subseteq[ b,F_0 )\`. The allegedly nontrivial zero-critical-count hypothesis is then automatic; the next typed links to newly selected top witnesses are artificially all zero. This is another age-level zero-tail argument in disguise, not witness-preserving diary progress.

**Corrected English statement, replacing the restricted interface above:** after the first actual finite stage, prescribe a *fresh* entire typed column \(c_\mathrm{next}:\mathbb N\times \mathrm{Fin}(d)\to\{0,1\}\) with
\[
  c_\mathrm{next}(p,t)=c_1(p,t)\quad\text{for every }p<F_0,\ t\in \mathrm{Fin}(d).
\]
Beyond \(F_0\), the values of \(c_\mathrm{next}\) are completely free and may retain **positive bits on already chosen selected original witnesses**. Old-prefix locality gives \(G_{B_{[0,F_0),c_\mathrm{next}}}=G_{B_{[0,F_0),c_1}}=\mathrm{middle}\) without an extra original-graph condition. For \(N=F_0+m\), require the **genuinely nontrivial** certificate
\[
 \forall U\ \operatorname{originalCriticalCount}
 (E,\ell,d,F_0,c_\mathrm{next},U,m)=0.
 \tag{**}
\]
Apply the verified neutral-interval theorem to \(c_\mathrm{next}\) itself and derive \(G_{B_{[0,N),c_\mathrm{next}}}=\mathrm{middle}\). Then the second genuine physical cover at \(N\) uses the *same* full \(c_\mathrm{next}\). Its new column \(c_2\) agrees with \(c_\mathrm{next}\) at **every** \(p<N\), so required positive old-to-future passing bits on the retained first-stage original witness set \(W_0\subseteq[0,N)\) are actually preserved, not reset.

This is conditional and finite. The original first-stage universal top witness has type relative to the original first-stage finite sorts, and the new theorem does not prove how its physical image is embedded into the evolving future-sort set, nor guarantee (**). The theorem may be useful as a strict interface precisely because its neutrality premise now carries the real combinatorial obstruction. No global validation mark.

**Added hostile checks:**
- The unchanged first-stage \`c_1\` is zero for every \(p\ge F_0\), so any theorem only preserving that column after \(F_0\) should be marked as an age-only result, not a positive-witness-preserving construction.
- Do not infer (**) from first-stage realization, from the \(K_\ell\)-free graph assumption, or from a finite upper-age equality at \(F_0\).
- Equality of old-prefix columns is needed on the *entire* original prefix \([0,F_0)\), including parameters, reserved blocks and unused gaps, not only selected originals.
- Keep \`W_0\` actual original indices below \(N\); if a future sort dimension changes, prove transport separately. A typed-column identity without a common sort dimension is ill-typed.
- The second stage preserves the newly specified \(c_\mathrm{next}\), not the all-zero tail of \(c_1\). This is a meaningful semantic strengthening despite similar surface proof steps.
