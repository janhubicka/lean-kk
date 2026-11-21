# Track F — canonical graph-age antitonicity under genuine chronological type refinement

21 November 2026. English argument and adversarial audit **before Lean**. Complements the code-history work (#424 actual code, #430 precode rigidity, #433 survivor resynchronization and draft #436 genuine intermediate age).

## Statement

For any finite family of genuine source/target Henson one-types, two fronts `u_i` at old level m and `w_i` at later common level M, suppose `m≤M` and `u_i≤w_i` in the **full chronological extension order** (positive AND negative old bits preserved).

For every nonempty finite sort support S, the old actual common-positive-neighbour pool is contained in the later common pool: if an old x<m is adjacent to all sorts in S, those bits are unchanged at every later type w_i and x<M. Hence true directed clique capacity can only increase, and the true raw age `ell−1−capacity` can only decrease.

Consequently the canonical integer-witness graph-age profile at the later front is pointwise ≤ the earlier canonical profile. This follows from a second abstract fact: the normalized integer graph-age canonicalizer is monotone in its RAW bounds. Indeed every full integer clique vector feasible under stricter bounds B is also feasible under looser C whenever B≤C, so its finite suprema satisfy `G_B≤G_C`.

## Sandwich application

For three genuine fronts `u≤p≤w` at common levels m≤h≤M, one obtains

`CanonicalAge(w)≤CanonicalAge(p)≤CanonicalAge(u)`.

If the endpoint canonical profiles are equal, then the intermediate profile is exactly equal to both endpoints (antisymmetry). This excludes EVERY unrecorded strict complete age change between checkpoints, including hidden mixed/triple support changes, independent of whether raw numerical bounds are redundant.

This sandwich lemma is what the frozen code and split arguments invoke when they claim that profiles cannot change between two equal synchronized endpoint classes. It does NOT by itself prove endpoint equality, which remains a separate geometric output of #410/#433.

## Adversarial audit

1. The target/source types must be genuine SAME-LEVEL tuples at each stage. The old level m and new level M can be different, but every old type is at m and every later type at M.
2. We explicitly assume m≤M, rather than inferring it by choosing an arbitrary sort in `Fin(d)`—the d=0 case must work vacuously.
3. The chronological extension order must preserve both positive and negative old bits; mere inclusion of positive neighbours would suffice for the RAW antitone direction but not for the history’s complete prefix invariant.
4. The common-neighbour pool for the empty support is the full prefix, and its behavior is irrelevant. All age comparisons are restricted to nonempty admissible supports.
5. Directed finite clique capacity is monotone under pool inclusion for an arbitrary directed E; no external symmetry assumptions are needed for this set-theoretic step.
6. Nat subtraction is antitone in the subtracted clique capacity, including truncated values; do not accidentally reverse the inequality.
7. The RAW function itself need not be a genuine graph age. Canonicalizer monotonicity holds for arbitrary raw bounds because feasible vector inclusion is direct.
8. Canonicalizer monotonicity cannot be replaced by numerical equality of RAW and canonical supports; redundant support inequalities are allowed.
9. In the true history application, the intermediate target prefixes at each numerical cut must be constructed from actual future types, not shadow coordinates or hypothetical inconsistent columns.
10. A comparison of FULL canonical age functions, rather than only singleton or pair values, is required to exclude hidden triple-support events.
11. Sandwich equality requires both endpoint profiles to agree. A single upper/lower inclusion cannot force no intermediate event.
12. If one only knows endpoint equality of finite classes, the equality of their genuine canonical age functions follows by the verified integer extension-profile characterization, but that identification is a separate point; the corollary below assumes numerical canonical endpoints equal to avoid conflation.
13. The theorem has no target embedding e, no coding-node fibre, and no actual diary order; it is purely physical finite Henson prefix age monotonicity.
14. The unchanged-black manuscript rule continues. A correct Lean proof of this component cannot promote history-realization or BRD lower-bound validation markers by itself.
15. The compatibility and survivor-selection theorems (#410/#433) provide some relevant endpoint equivalences, but matching the actual intermediate target tuple at a prescribed coding cut is still a separate obligation.

## Lean acceptance

Prove named endpoints (a) monotonicity of `integerGraphAgeCanonical` under pointwise raw `AgeLe`, (b) actual `trackFCommonRawAge` antitone under coordinatewise chronological extensions at common levels, (c) canonical actual prefix profile antitone, and (d) three-stage sandwich equality when both endpoint canonical profiles coincide. Each new theorem requires exact-head Lake build and strict standard-only named axiom check. No pre-proved diary characterization is used.
