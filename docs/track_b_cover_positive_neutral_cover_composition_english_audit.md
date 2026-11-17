# Track B — real cover / positive-neutral / cover composition

**English proof and adversarial review written before Lean. 17 November 2026.**

This is a precise composition of two already kernel-checked finite physical existence results, **not** an assertion about an unbounded diary.

Fix the SAME normalized \(K_\ell\)-free left-dense Henson original graph \(E\) and SAME finite future-sort dimension \(d>0\). Fix genuine covers
\[
  \mathrm{lower}\lessdot\mathrm{middle}\lessdot\mathrm{upper}
\]
at respective supports \(T_1,T_0\), with actual physical age-cover parameters \(r_1,r_0\) satisfying the exact equations used by \`PhysicalCanonicalCoverStage\`. Let the old canonical age at original prefix \(b\) under complete column \(c\) be *pointwise* upper. Choose a strictly positive size \(r_N\le r_0\).

**First cover.** Invoke \`henson_leftDense_exists_physical_finite_canonical_cover_stage\` at b. It produces actual reserved original clique \(Q_0\) of cardinal \(r_0\), cutoff \(F_0\), complete gap-aware column
\(c_1=\operatorname{supportBlockGappedColumn}(b,Q_0,T_0,c)\), and full canonical age *middle* at \(F_0\). It also supplies a real finite numerical-H uniform positive-support future stage. All q in Q0 are actual originals in \([b,F_0)\).

**Automatic anchor.** Since \(Q_0\) is a genuine directed clique and every q in Q0 has **all** prescribed positive column bits on support \(T_0\) under c1, the old original common-neighbour pool \(X_{[0,F_0),c_1}(T_0)\) contains Q0. Thus its directed clique capacity is at least \(r_0\ge r_N\). This is not an additional hypothesis: it is *derived* from the first actual reserved block.

**Real positive-neutral stage.** Invoke \`henson_leftDense_exists_anchored_positive_neutral_block\` at the ACTUAL original cutoff \(F_0\), with anchor R=Q0, column c1, support T0 and size rN. It produces a new real positive-T0 clique QN of size rN, cutoff FN, complete gap-aware column
\(c_2=\operatorname{supportBlockGappedColumn}(F_0,Q_N,T_0,c_1)\),
and one real finite numerical-H positive-support stage. Its whole RAW old-column function is literally unchanged:
\[
B_{[0,F_N),c_2}=B_{[0,F_0),c_1}.
\]
Hence its full canonical age is exactly middle; this hPrior is **derived**, not postulated. The first and new reserved cliques are physically cross-nonadjacent in BOTH directions. The column at every q in QN is genuinely positive on T0, so this is **not** zero-tail padding.

**Second cover.** Invoke \`henson_leftDense_exists_physical_finite_canonical_cover_stage\` again at FN with full column c2 and the second genuine cover lower ⋖ middle. It gives a third real reserved clique Q1, actual cutoff F1, final entire original canonical age lower and a finite numerical-H stage. The new Q1 is physically isolated from EVERY earlier original including both Q0 and QN, in both directions. Thus all three positive/reserved physical stages occur in one fixed E, with exact original chronology and no retroactive edge change.

### Hostile checks

1. \(r_N>0\) matters: without it no genuinely positive new original is built. The first actual cover's side equations imply \(r_0<\ell\), so \(r_N<\ell\) follows.
2. The first cover Q0 must be a genuine clique, not just a set of positive fronts. Its clique **capacity** equals cardinality.
3. The new stage's full typed column c2 must be built by \`supportBlockGappedColumn\`, not by replacing c1 with an all-zero tail. Any originally positive c1 bits below F0 must be retained.
4. The raw age equality holds on **every nonempty support**, including proper subsets of T0. It uses containment \(X(T_0)\subseteq X(U)\) for \(U\subseteq T_0\).
5. The new block QN is not assumed or forced to be selected top witnesses from the first stage. Each uniform top witness f,M is independently existential.
6. The second canonical-age equation is derived from the neutral raw equality and the first cover. Its hPrior must not be inserted as an independent input.
7. Both fresh blocks are isolated from the complete earlier actual original prefix; this yields Q0–QN, QN–Q1 and Q0–Q1 nonedges in BOTH directed orientations.
8. The theorem does not prove *arbitrary prescribed* positive continuation columns are neutral. The new block is specifically completely isolated to earlier originals and uniformly positive on T0.
9. No arbitrary split/coding sort-domain changes occur; d is fixed. No complete auxiliary \(Kpt\) old/upper dependent \(L^+/E\) (I1–I3/B3) source synchronization is asserted.
10. The global bounded resolved copy, a common labelled inverse source orbit, and exact upper/lower big Ramsey degree characterization remain PENDING; the result is a three-stage source-exact finite construction.

**Acceptance:** require exact-head full Lean build and strict central named transitive-axiom gate (four initial new endpoints plus the new composition theorem), no extra axioms, and separately check the English and Lean statements really agree.
