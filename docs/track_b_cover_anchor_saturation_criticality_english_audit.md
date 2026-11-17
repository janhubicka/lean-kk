# Track B — exact cover-anchor saturation and the selected-witness criticality obstruction

**17 November 2026. English mathematical proof and adversarial review before Lean source.**

## Claim 1: a genuine canonical cover saturates its distinguished support

Fix an actual original prefix P=[0,b), full future-sort column c, a genuine finite lower/upper integer-witness age cover at support T and physical reserved block Q⊂[b,F). Write
\[
 X_P(T)=\{p<b:\ c(p,t)=1\ \forall t\in T\},\qquad a=\rho_E(X_P(T)).
\]
Assume the complete initial canonical age \(\operatorname{Can}(B_{P,c})=\mathrm{upper}\), the exact side equations
\(\mathrm{upper}(T)=\mathrm{middle}(T)+1\) and
\(\ell=\mathrm{middle}(T)+r+1\), and the true clique Q has cardinal r, is isolated from every original p<b (both E directions), and all intervening original gap columns are zero.

The canonicalizer is pointwise below its literal RAW bound. Hence
\[
 \mathrm{middle}(T)+1=\mathrm{upper}(T)
 \le \ell-1-\rho_E(X_P(T))
 =\mathrm{middle}(T)+r-\rho_E(X_P(T))
\]
with Nat truncation handled by the positive left-hand side. Therefore **\(a<r\)**, in particular \(r>0\). This is a real inequality, not a new assumption about the selected front.

The verified genuine gapped support-block pool identity says
\[
 X_{[0,F),c_1}(T)=X_{[0,b),c}(T)\cup Q,\qquad
 c_1=\mathrm{supportBlockGappedColumn}(b,Q,T,c).
\]
Because every old-to-Q original E forward bit is zero, actual directed clique capacity of this union is a MAX of the two capacities. Q is a genuine directed clique of cardinal r, so
\[
 \rho_E(X_{[0,F),c_1}(T))
 =\max\{a,r\}=\boxed{r}.
\]
In particular the entire Q is a maximum common-neighbour clique at the distinguished T. Every old gap original has literally zero future bits and is not in this pool.

## Claim 2: a later full-anchor-linked positive vertex is critical

Let v≥F be any genuine later original with BOTH E directions positive to **every q∈Q**. Let \(\tilde c\) be a full continuation column agreeing with c1 on every original p<F, and suppose \(\tilde c(v,t)=1\) for **every t∈T**. By old-prefix locality
\(X_{[0,F),\tilde c}(T)=X_{[0,F),c_1}(T)\), of capacity r. Since each q∈Q belongs to the new v's **mutual** old neighbours, the mutual-neighbour pool contains the old clique Q of cardinal r. It is also a subset of the full old common-neighbour pool, whose capacity is exactly r. Hence its capacity equals r:
\[
\rho_E(M_E(X_{[0,F),\tilde c}(T),v))
 = \rho_E(X_{[0,F),\tilde c}(T))=r.
\]
Together with \(\tilde c(v,t)=1\) for all t∈T, this is exactly the existing \`originalCriticalSupport\` predicate. Its RAW T-bound therefore drops by one under natural subtraction. If the *actual augmented original prefix* [0,F)∪{v} is genuinely K_ell-free, the drop is **strict**, even when the new bound is zero, by the earlier checked \`finiteOldColumnRawBound_insert_strict_drop_iff_critical_of_safe\` theorem.

## Scope and hostile checks

1. A first physical canonical cover forces its distinguished new old common-neighbour cap to be exactly r; it is NOT an extra saturation hypothesis. The proof needs the whole initial **canonical** reference age upper and the exact two integer-cover side equations.
2. The inequality canonical≤RAW is essential; the reverse inequality would be invalid.
3. Directed clique capacity and BOTH-directed adjacency matter. One-way links from v to Q do not give a common mutual-neighbour clique.
4. The actual old/common pool includes all originals below F. No selected-front or missing-gap projection is used.
5. Q must be a genuine physical clique of cardinal r, isolated from the entire old prefix. An arbitrary set Q with card r could have smaller clique capacity.
6. The later column \(\tilde c\) must agree at **all original p<F**, including Q, old selected vertices, parameters and gaps; preserving only canonical ages is insufficient.
7. To be critical on T, v must have a positive future column on ALL sorts of T. Positive bits on only some sorts do not suffice.
8. The critical predicate itself does not require global safety. To infer strict raw decrease from the Nat-subtraction formula, genuinely K_ell-free enlarged original pool safety is required.
9. This is an obstruction only to **RAW-neutrality** of such a fully linked positive vertex. Canonical ages may still be unchanged by a redundant raw constraint. Do not claim a canonical cover happens automatically.
10. An isolated positive neutral block from PR #326 is perfectly compatible: it is deliberately **nonadjacent** to Q, so it avoids this criticality. That is exactly why it cannot be identified automatically with a selected top witness that must see all of Q.
11. The actual first finite universal top stage forces appropriate ordinary-L positive incidences to Q, but here that linkage is still an explicit hypothesis on v; identifying a specific f(W) physical image and its later sort support requires a separate adapter.
12. No coherent unbounded resolved diary, full Kpt I1/I2/I3/B3, labelled inverse-source orbit or big Ramsey bound is implied.

**Acceptance:** exact-head full Lean build and strict named axiom reports, with zero custom axioms/sorryAx, before any green/blue manuscript pin. The result should strengthen the targeted Track B TODO, not resurrect old abandoned global recurrence text.
