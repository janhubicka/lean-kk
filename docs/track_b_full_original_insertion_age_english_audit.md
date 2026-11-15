# Track B — exact full-support original insertion and stage-invariant audit
**15 November 2026. English mathematical proof BEFORE Lean.**

## Purpose and scope

The finite neighbourhood checker already characterizes when a genuine new original can be inserted without producing a forbidden clique. It **does not** tell us how the *actual full old-prefix continuation age* changes. Isolated-clique-block arithmetic from Track A cannot be applied to a general selected, split, or coding original which may link to old selected vertices, already reserved blocks, and gap indices.

This note proves an **exact one-original recurrence** for every supported old-neighbourhood clique capacity under arbitrary original-to-original links. It applies to directed edge tables (even before Henson symmetry), requires no named reserved-block decomposition, and incorporates every previous original. The nonexpansion consequence is a new sufficient condition for a stage to be *raw/canonically age neutral*, but NOT for Algorithm 5.4 to call the stage boring.

## Statement 1: literal old common-neighbour pool

Fix finite old original pool \(P\), a **fresh** original \(v\notin P\), a full typed future column \(c:\mathbb N\times d\to\{0,1\}\), and a nonempty admissible support \(U\). Write

\[
X_U(P)=\{p\in P:\forall t\in U,\ c(p,t)=1\},\quad
\operatorname{live}_U(v)\iff \forall t\in U,\ c(v,t)=1.
\]

The exact set identity, which in fact does not require freshness, is
\[
 X_U(P\cup\{v\})=
 \begin{cases}
    X_U(P)\cup\{v\}, & \operatorname{live}_U(v),\\
    X_U(P),&\text{otherwise.}
 \end{cases}
\]
Proof: expand the defining filter on \(P\cup\{v\}\). Each old \(p\in P\) retains exactly its old membership because the same whole typed column \(c\) is used on both sides. Only \(v\) can be added, and it belongs precisely when every sort in \(U\) is positive. **The old column must not be retroactively edited.**

## Statement 2: exact mixed old-neighbour clique-capacity update

For any directed graph \(E\), finite \(X\), and fresh \(v\notin X\), define the *mutual* old-neighbour set
\[
 M_E(X,v)=\{x\in X:E(x,v)=E(v,x)=1\},\qquad
 \rho_E(X)=\max\{|S|:S\subseteq X \text{ is a complete directed clique}\}.
\]
The already kernel-checked theorem \`finiteDirectedCliqueCapacity_insert_eq\` states
\[
\rho_E(X\cup\{v\})
 =\max\big(\rho_E(X),\,1+\rho_E(M_E(X,v))\big).
\]
A directed clique either avoids \(v\) or contains it; in the latter case deleting \(v\) produces a clique in \(M_E(X,v)\). Conversely a maximum clique in \(M_E(X,v)\) extends by \(v\), using **both** directed edges. Note that \(M_E(X,v)\) is generally neither the whole selected-front passing set nor the entire linked-unreserved pool from a chosen block decomposition.

Consequently the exact raw bound at support \(U\) after adding \(v\) is
\[
 B_{P\cup\{v\}}(U)=\ell-1-
 \begin{cases}
 \max\{\rho_E(X_U(P)),1+\rho_E(M_E(X_U(P),v))\},
     &\operatorname{live}_U(v),\\
 \rho_E(X_U(P)),&\neg\operatorname{live}_U(v).
 \end{cases}
\]
The subtraction is *natural truncated subtraction*. This is a literal \(\mathbf H\) original-graph raw-age formula, **not** an assertion about auxiliary \(E\) of the Kpt \(L^+\) tree.

## Statement 3: age-neutral stage criterion

For every support not positively seen by \(v\), the raw bound is unchanged. On a positively seen support \(U\), the **capacity** is unchanged if and only if
\[
1+\rho_E(M_E(X_U(P),v))\leq \rho_E(X_U(P)).
\]
Thus, if this inequality holds simultaneously on **every** nonempty admissible support positively seen by \(v\), we get pointwise \(B_{P\cup\{v\}}=B_P\), and hence equality of the integer-witness canonicalizers \(G_{B_{P\cup\{v\}}}=G_{B_P}\). The converse from equality of *raw bounds* to equality of capacities requires avoiding saturation: \(\ell-1-\rho\) can equal \(0\) for different capacities \(\rho\geq\ell-1\).

For a **consecutive actual prefix** \([0,b)\), use \(\operatorname{Finset.range\_succ}\) with fresh \(b\notin[0,b)\) to derive the exact physical one-original formula at \(b\). The positive-support budget criterion can be checked after every insertion. This is substantially more general than forcing the entire new column to zero: positive incoming bits are allowed if they do not create a *larger old common-neighbour clique*.

## Statement 4: composing safety and age without circularity

For a symmetric loop-free graph \(E\), \(\ell>0\), if the actual prefix \([0,b)\) is \(K_\ell\)-free and the **complete** next original neighbour test
\[
 \operatorname{finiteNeighbourCliqueCheck}(E,b,\ell-1,
                      x\mapsto E(x,b))=\mathrm{false}
\]
passes, then \([0,b+1)\) is \(K_\ell\)-free by the kernel-checked one-point iff. If in addition the age-neutral budgets from Statement 3 hold for the very same full typed column \(c\) at \(b\), the actual raw and canonical ages of the two successive prefixes are identical. These are **independent** conditions: no theorem here manufactures the next \(E\)-column, the positivity witnesses, or a prescribed **age drop**. It merely composes two existing kinds of finite certificate correctly.

This yields the exact shape of a later \`ResolvedStageInvariant\` record:
- actual original cut and *unchanged* full prior graph and future columns;
- complete proposed neighbourhood checker, including old reserved, selected, split/coding, and gap originals;
- every-support literal old-capacity update or the age-neutral budget; and
- separately, real dependent Kpt source/microevent equality with normalized cut labels.

The last item is NOT implied by the first three.

## Adversarial checks and exclusions

1. **Freshness essential:** for \(v\in X\), the formula with an extra \(1+\rho_E(M_E(X,v))\) can double-count \(v\). The common-neighbour set identity itself remains true, but the exact max capacity formula is used only when \(v\notin P\).
2. **Both directed bits essential:** an incoming-only edge \(E(x,v)=1\) with \(E(v,x)=0\) does not let \(x\) join a directed clique containing \(v\).
3. **Old typed columns fixed:** changing \(c(p,t)\) for any \(p\in P\) invalidates the identity \(X_U(P\cup\{v\})=X_U(P)\cup\cdots\).
4. **All supports:** positivity on one marked sort does not mean positivity on a support containing two sorts. Use \(\forall t\in U\), not \(\exists t\in U\).
5. **Full old pool:** \(X_U(P)\) includes *every* earlier original whose future columns are positive, not just selected vertices or intended reserved blocks.
6. **No cross-block shortcut:** a new original may join an old reserved vertex and an old selected/parameter clique; the mutual-neighbour formula detects it.
7. **New positive gap:** a gap original with a positive column can affect the bound just like any other old original.
8. **No cardinal replacement:** \(|M_E(X,v)|\) is not the clique capacity \(\rho_E(M_E(X,v))\).
9. **Raw-vs-canonical distinction:** raw pointwise equality implies canonical equality, but general canonical equality does not force raw equality.
10. **Clipping:** even pointwise raw equality can hide increased capacities if both exceed the \(\ell-1\) threshold; do not claim an iff without hypotheses.
11. **No parameter closure from ordinary \(L\):** the K4 auxiliary \(q_2\) cut 10/22 regressions remain; full \(L^+\) microevents must be checked independently.
12. **No new-root prefix saturation:** seeding all Kpt ancestors forces all I1 cuts, so the source recursion must use actual bare Kpt originals and genuine closure.
13. **No rank identification:** this prefix index \(b\) is a base-original index, not an automatically aligned Kpt source-coordinate cut \(c\).
14. **No existence from a certificate alone:** complete-column left density gives a selected original for a safe prescribed old neighbour column, but the present theorem does not establish that the intended diary generates safe columns at every recursive stage.
15. **Unbounded recursion still open:** a collection of correct finite one-step implications does not produce an infinite compatible chosen schedule, a common labelled source orbit or an exact BRD classification.

Independent Python directed-graph referee, fixed seed 15026, checked **12,000** random cases over \(1\leq n\leq 6\), \(1\leq d\leq4\), arbitrary directed edge bits and arbitrary typed columns/supports. Every instance satisfied the literal pool identity, the exact max capacity update, and capacity monotonicity. This is supplementary evidence, **not** a Lean proof and not a proof of the unbounded schedule.

**Validation policy:** English proof here precedes Lean code. New module claims remain **UNVERIFIED** until a full exact-head Lean CI and a transitive named-axiom audit pass. Do not add new green manuscript marks, edit frozen black prose, or re-add collaborator-deleted TODOs on this basis.
