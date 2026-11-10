# Exact gluing continuation age as inequalities for every L-only clique witness

**10 November 2026 — English proof first, adversarial audit before dependent Lean.**

## Why this is the next interface

The now-verified finite gluing theorem checks the absence of a K_ell clique in a union of old P, reserved Q, gaps G and arbitrary future W. The new independent support-witness theorem identifies the bound on \`cap_E(U)\` for U selected by a sort support T with an inequality against the T-part of **every** finite clique inside W. Combining them is the correct way to approach corrected-B3 age rather than inspecting only the **actual** selected-top originals in H.

## Statement A: arbitrary directed graph and arbitrary W

Fix any directed Boolean graph E on Nat, threshold ell, and finite P,Q,G,W. Let \(\sigma:\mathbb N\to\operatorname{Fin}(d)\) be a sort labelling and \(T\subseteq\operatorname{Fin}(d)\) a chosen support. Set
\(U=\{w\in W:\sigma(w)\in T\}\).

Require exactly the gluing hypotheses already proved for the four-pool classification:

- \(Q\cap U=\emptyset\), which is **not automatic** if W is an arbitrary hypothetical continuation;
- all old-to-reserved E(p,q) bits vanish;
- all gap-to-future E(z,w) bits vanish;
- BOTH directions of each reserved-to-future bit E(q,w), E(w,q) equal decide(\(\sigma(w)\in T\));
- the entire P∪Q∪G passes the K_ell clique checker.

Then
\[
\begin{split}
\neg K_\ell(P\cup Q\cup G\cup W)
\quad\Longleftrightarrow\quad&
\neg K_\ell(P\cup W)\ \land\\
&\forall s\subseteq W\
  \bigl(\operatorname{Cliq}_E(s)\Longrightarrow
  \operatorname{cap}_E(Q)+|\{w\in s:\sigma(w)\in T\}|<\ell\bigr).
\end{split}
\]
The proof is a direct composition: rewrite each \(\mathbf1_{w\in U}\) as \(\mathbf1_{\sigma(w)\in T}\) using w∈W (an iff, not only an implication), apply the exact finite gluing iff, and replace \(\operatorname{cap}_E(Q)+\operatorname{cap}_E(U)<\ell\) by the universal clique-witness equivalence. The latter is valid even when W or U is not a clique, and even when ell=0.

## Statement B: literal finite numerical-H reserved prefix

Take a symmetric base E_0; form the ordinary binary L-relation of the ACTUAL \`finiteNumericHL (normalizedGraphModel E_0) k M\`. Let
\(Q=\operatorname{reservedBlockNumericPrefix}(k,N,a,g)\), with \(a<r\le k+1\), \(g\le k\) and the exact complete original reserved clique \(N,\ldots,N+r-1\). Keep P,G,W and σ,T arbitrary; assume the exact same old/reserved, gap/future and both-direction **L** support columns plus the past test.

The merged physical capacity theorem gives \(\operatorname{cap}_{L_H}(Q)=a\) for g<a and a+1 otherwise. Thus the universal witness inequality becomes
\[
\forall s\subseteq W\
\bigl(\operatorname{Cliq}_{L_H}(s)\Rightarrow
 (a+\mathbf1_{g\ge a})+|\{w\in s:\sigma(w)\in T\}|<\ell\bigr).
\]
This result is **about any W with the prescribed columns**, not only W consisting of selected top coordinates that are already realized by the Henson original. It is the correct finite continuation criterion to feed into the integer graph-age canonicalizer.

## English proof and precise remaining gap

The raw support inequality above matches the desired one-coordinate bound \(\ell-1-a'\), where \(a'=\operatorname{cap}(Q)\) (provided \(a'<\ell\)); the already-verified \`finiteCliqueSupportCapacity_raw_iff_all_witnesses\` makes that natural subtraction step explicit. The graph-age canonicalizer, however, uses **normalised integer multiplicity vectors** over all nonempty supports, not arbitrary finite graph witnesses. Converting every finite clique s to such a vector and proving that all support inequalities correspond remains the next formalization target. An additional existence step must realize every age-admissible L-only continuation witness in a compatible Henson extension, preserving all other colours and auxiliary E/parameter records.

## Adversarial checks

1. **No future pool clique assumption.** \(\operatorname{cap}(U)\) is generally less than \(|U|\); the right side ranges over every clique subset s of W, not a single maximum clique of all W.
2. **Outside-support obstruction.** The separate P∪W K_ell-free test cannot be dropped. A forbidden clique may live entirely outside the support T, where the universal selected-count inequality sees zero.
3. **Past obstruction.** P∪Q∪G must pass its own K_ell test; new support bounds cannot repair an existing forbidden clique.
4. **Both L directions.** Rewriting \`hSupport\` requires the exact equality of E(q,w) and E(w,q) with decide(sort(w)∈T); reverse orientation is not automatic for a generic directed graph.
5. **Non-overlap Q∩U.** The gluing theorem needs this; the abstract support filter does not force it, unlike the special genuine later-top future pool.
6. **Zero/support boundary.** If T is empty then U is empty, and the universal s=∅ clause detects \(\operatorname{cap}(Q)<\ell\), not an implicit vacuous truth.
7. **Height condition.** The physical capacity formula needs a<r≤k+1. Dropping it produces the known top-generation-tie counterexample.
8. **Actual H binary vs Kpt auxiliary E.** The support bits are ordinary L binary atoms of finiteNumericHL, not H+ parameter-incidence E.
9. **Finite carrier.** For age interpretation, the numerical pivot and all P/G/W coordinates must lie below the chosen M. A theorem about the total binary table alone does not guarantee carrier membership.
10. **All W does not mean existence of all W.** The equivalence is conditional on the prescribed graph table and edges; it does not build Henson extensions or establish the family of all possible continuation types.
11. **Sort multiplicities.** The sort map need not be injective; a clique can contain many vertices of the same sort. Counting supported vertices must preserve multiplicity.
12. **No arbitrary type closure.** The corrected-B3 test also quantifies over auxiliary parameter-closed source types; L-only clique tests are just its graph-age component.

## Validation contract

First prove statement A directly from two existing kernel-checked theorems. Then substitute the genuine numerical H capacity (statement B), without weakening any edge hypothesis. Register named transitive-axiom reports and require the full hosted build to pass. Do not mark the manuscript green for full B3 or common source until normalized integer-age vectors and parameter-closed source agreement have been established.
