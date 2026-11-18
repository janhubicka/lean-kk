# Track B: necessary and sufficient active-pivot capacity budgets (English proof before Lean)

## Mathematical statement

Let E be a fixed original Boolean graph, v<H a fixed original pivot, a(p,u) arbitrary complete background columns on all nonpivot originals below H, beta(u) pivot's new passing bits, and let F be a **genuine normalized positive integer graph age** on e new sorts with clique parameter ell.

For every admissible nonempty support U, set

 X(U)={p<H:p!=v and a(p,u)=1 for all u in U},
 Y(U)={p in X(U): E(p,v)=E(v,p)=1},
 r(U)=maximum directed clique size in X(U),
 m(U)=maximum directed clique size in Y(U).

Let Bplus be the actual full-prefix raw bound under the column which is a outside pivot v and beta at v. Then the following are equivalent:

 (I) F <= canonical(Bplus) pointwise on ALL supports;

 (II) for EVERY admissible support U,
      r(U)+F(U) <= ell-1
      and, if beta is positive on all of U,
      1+m(U)+F(U) <= ell-1.

No extra K_ell-free hypothesis enters this exact equivalence; genuine F and its support positivity are needed for both directions.

## Proof

Already verified finite pivot insertion shows that Bplus(U)=ell-1-rho_new(U), where rho_new(U) is r(U) if beta has a zero on U, otherwise max(r(U),1+m(U)).

By the universal property of normalized integer-witness graph-age canonicalization:

   F <= canonical(Bplus) iff F <= Bplus,

provided F is itself an integer graph age. For the forward implication use canonical(Bplus)<=Bplus; for the reverse implication use that canonical(Bplus) is the greatest feasible graph age below Bplus.

For a genuine age F, F(U)>=1. Hence for natural truncated subtraction,

  F(U) <= ell-1 - t  iff  F(U)+t <= ell-1.

The positivity assumption is essential: for F(U)=0 the left inequality is automatic even when t>ell-1. Apply this to the cases of rho_new and distribute the maximum. If beta has some zero on U, only r(U) must be bounded; if beta is all positive, both r(U) and 1+m(U) must be bounded. This is exactly condition (II).

This proves an exact **full-support** stage budget criterion. It is not merely a sufficient cardinal bound and it retains arbitrary nonzero columns on protected selected/coding/reserved originals.

## Adversarial audit

1. Do NOT omit the positivity F(U)>=1: the natural-subtraction equivalence fails at zero.
2. F must be a genuine normalized integer graph age: raw functions have no greatest-age theorem.
3. This is comparison with a target age F, NOT an assertion that all child sorts are inhabited.
4. Every support is checked; singleton budgets alone fail for mixed cliques (K4 pair regression).
5. The actual pivot is excluded from X, avoiding double counting.
6. Y uses bilateral E-links, not only one orientation.
7. All actual nonpivot originals p<H, including active gaps, contribute to X and Y.
8. A positive beta only on some children does not add the pivot to supports containing a zero child.
9. F(U)+1+m(U) may exceed ell-1: then no full age F can survive this literal passing pattern.
10. The theorem does NOT assert that a requested diary successor preserves F; if the intended transition requires a lower age, substitute that desired lower target and check both inequalities.
11. No uniqueness of the full canonical new age follows from F<=canonical(Bplus); other coordinates may increase above target.
12. A further exact equality can be obtained by bounding canonical(Bplus) above the intended target, which requires additional witness/saturation arguments.
13. The finite Henson realization theorem can realize the resulting full raw-feasible profile, but does not recover numerical-H E/closure source labels.
14. The one common stage certificate remains essential for using this in an actual schedule.
15. Global Kpt I1/I2/I3/B3, inverse-source orbit and BRD theorem remain open.

## Verification plan

Formalize this equivalence on a branch stacked on the verified exact active-pivot capacity branch; run strict axiom reports and full Lean build. Do not replace black frozen manuscript text or mark global characterization validated.
