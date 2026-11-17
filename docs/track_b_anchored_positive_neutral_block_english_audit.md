# Track B — genuine positive age-neutral Henson blocks anchored by earlier clique capacity
**17 November 2026. English proof and adversarial audit BEFORE Lean code.**

## Problem

The verified zero-tail bridge inserts arbitrarily many original indices but all their future-sort bits are zero. The subsequent genuinely positive-column bridge requires a **separate** all-support zero-critical-count hypothesis on the prescribed new continuation. A natural new question is whether the real Henson enumeration *itself* permits any positive neutral stage for which neutrality follows from the constructed old source rather than being assumed.

The answer is YES for a sharply delimited class of blocks. This is a source-exact finite **ordinary-L** construction and does not identify the resulting new block with an arbitrary selected original of the desired infinite resolved diary.

## Capacity-dominated isolated support blocks

Let E be any directed graph on the true original indices. Fix an actual finite original set P, complete future-sort column c, and an admissible nonempty future support T. Write
\[
  X_P(U)=\{p\in P:\ c(p,t)=1\text{ for all }t\in U\},\quad
  \rho(Z)=\text{directed-clique capacity of }E|_Z,\quad
  B_P(U)=\ell-1-\rho(X_P(U))
\]
(using truncated subtraction for the final expression).

Suppose a finite new original block Q is disjoint from P and has **no forward original E edges P→Q**. Give each q in Q complete positive future columns exactly on T, and leave the old columns unchanged. The already verified source-exact isolated-support update is
\[
 B_{P\cup Q}^{(T)}(U)
 =\begin{cases}
  \ell-1-\max\{\rho(X_P(U)),\rho(Q)\},& U\subseteq T,\\
  B_P(U),& U\nsubseteq T.
 \end{cases}
 \tag{1}
\]
A crucial monotonicity direction: if \(U\subseteq T\), then \(X_P(T)\subseteq X_P(U)\), hence \(\rho(X_P(U))\geq\rho(X_P(T))\). Therefore, if
\[
 \rho(Q)\leq \rho(X_P(T)),
 \tag{2}
\]
the maximum in (1) is always its OLD term; **the complete raw age is unchanged at every admissible support, not only after canonicalization**. The feasible labelled clique vectors and the integer-witness canonical age are unchanged as well.

A convenient sufficient certificate for (2) is an **already existing** genuinely directed clique \(R\subseteq P\) positive to every sort of T, with \(|Q|\leq|R|\) and Q itself a directed clique. Then \(R\subseteq X_P(T)\), so \(\rho(X_P(T))\geq |R|\geq |Q|=\rho(Q)\). Unlike an artificial zero tail, this construction contains an actually positive complete typed column on every q in Q.

## Realization in the same Henson original graph

Assume the usual normalized \(K_\ell\)-free Henson graph E and the explicitly stated one-point left density, \(2\leq\ell\), positive finite sort dimension d, a true original cut b, an existing nonempty anchor clique \(R\subseteq[0,b)\), and its complete typed columns \(c(p,t)=1\) for every \(p\in R\), \(t\in T\). Fix a positive size \(r\) with \(r\leq |R|\) and \(r<\ell\).

Use the already verified Henson real-reserved-clique/finite-universal-stage theorem at the **actual** original cut b with that same T, r and c. It constructs a real original clique Q of size r after b, isolated in both E directions from every original <b, and a cutoff F containing every intervening original index. The full column
\[
 c_1(p,t)=\begin{cases}
 c(p,t),&p<b,\\
 1_{t\in T},&p\in Q,\\
 0,&b\leq p<F,\ p\notin Q
 \end{cases}
\]
is exactly the source's \`supportBlockGappedColumn b Q T c\`, including *all* original gaps. Since (2) is now guaranteed by the earlier anchor R, the literal raw old-age at F is exactly the age at b, and therefore so is the canonical age. One physical finite numerical-H top-stage witness exists for the positive T-column in the unchanged E.

The resulting **age-neutral positive block is not automatically a selected diary node**: it is originally constructed as an isolated auxiliary block, and the future top-stage witnesses produced in the same invocation need not be coherent with an earlier chosen finite selected embedding.

## New composition with actual cover stages

After any first real physical canonical cover \(\mathrm{middle}\lessdot\mathrm{upper}\) at support \(T_0\), with reserved clique \(Q_0\) of positive size \(r_0\), every q in \(Q_0\) lies before the new cut \(F_0\), and the actual updated column \(c_1=\mathrm{supportBlockGappedColumn}(b,Q_0,T_0,c)\) is positive on all of \(T_0\) at each such q. Hence \(R=Q_0\) is an **automatically constructed anchor** for another isolated positive block on \(T_0\), of any size \(0<r\leq r_0\). Realize this truly positive but *raw-age neutral* intermediate block \(Q_\mathrm{neutral}\) at \(F_0\). This yields a later true cutoff \(F_\mathrm{neutral}\), a new complete column \(c_2\), and the derived full canonical age
\[
 G_{B_{[0,F_\mathrm{neutral}),c_2}}
 =G_{B_{[0,F_0),c_1}}=\mathrm{middle}.
\]
A second real physical cover \(\mathrm{lower}\lessdot\mathrm{middle}\) at any support \(T_1\), using the actual \(c_2\), can now be invoked at \(F_\mathrm{neutral}\). The new reserved clique is physically nonadjacent in both directions to every earlier original including Q0 and the neutral Q. The produced finite stages are individually genuine. The concatenation does **not** yet assert compatible finite selected-witness images.

## Adversarial audit: non-negotiable boundaries

1. The block Q must be **really isolated** from every prior original in P (at least all forward E atoms P→Q vanish), not merely disjoint from an abstract selected macro-front.
2. Condition (2) is only **sufficient**, not necessary. Without it, raw age can drop but canonical age may still remain equal due to redundant constraints.
3. If \(X_P(T)=\varnothing\) and Q is nonempty, adding a positive clique Q gives a new critical original on T. The original zero-tail argument does not apply.
4. If \(r>|R|\), the MAX in (1) may increase. Bounding only the count of positive sorts, or imposing K_\ell-freeness, does not prevent that.
5. Both graphs and columns are literal and unchanged: no edge rewiring, no bogus adjacency across original gaps, no re-enumeration of \(\mathbf H\).
6. For U⊆T, old support pools **grow** as U shrinks; reversing that inclusion gives a false argument.
7. For U not contained in T, *none* of Q enters X(U), because Q’s complete columns have 0 outside T. This handles supports overlapping T but not contained in it.
8. The proof uses clique **capacity** of actual mutual neighbours, not their cardinality. Full K_\ell-freeness does not imply positive raw support bounds.
9. A legitimate Henson reserved-clique theorem assumes true forbidden-family avoidance and the separate left-density property. Neither follows merely from a raw-age bound.
10. A neutral intermediate Q with positive T-column is not the same as a first stage’s selected top witness. It may have different physical old passing bits, and the second stage may still interfere with earlier selected future witnesses that lie beyond the old cutoff.
11. Fixed d is essential; split/coding sort dimension changes need an independent transport theorem. Ordinary-L age neutrality does not synchronize parameter-closed Kpt old/upper L+/E source events, full B3 or common labelled inverse sources.
12. The global bounded resolved copy, full labelled envelope comparison, BRD upper/lower theorem and independent-set counts remain PENDING.

**Validation acceptance:** full exact-head \`lake build\` and strict named transitive-axiom report (baseline 878 plus the newly registered endpoints), only \`propext\`, \`Classical.choice\`, \`Quot.sound\`, and no \`sorryAx\`. Add manuscript marks only to the literal finite component; black prose remains frozen.
