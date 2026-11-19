# Track F — from exact clique supports to the full canonical graph-age test

19 November 2026. English proof and adversarial audit written **before** Lean. This is a continuation of merged PR #383; black manuscript text is frozen.

## Genuine raw support monotonicity

Fix an arbitrary actual directed ordinary edge table E, prefix height h, a finite sort family Fin(d), and a family of complete old positive-neighbour sets U_i. For finite sort supports S ⊆ T, the physical common-old-neighbour pool for T is a subset of that for S, since the T-membership test imposes at least all the S-membership conditions. Finite directed clique capacity is monotone in the underlying vertex pool. Consequently

    Raw(E,U,h,S) = (ell-1) - cap_E(common(S))
                 ≤ (ell-1) - cap_E(common(T)) = Raw(E,U,h,T).

This is true including S=∅ and T=∅ as numerical statements; the later upper-bound theorem between the source and target requires nonempty supports. Natural-number truncated subtraction is harmless in this direction.

## Full-support age-test equivalence (new bridge)

Fix a finite B on abstract vertices [0,N), labels σ:[0,N)→Fin(d), and assume B is genuinely K_ell-free on that finite set. For each nonempty directed clique C⊆[0,N), let supp(C)=σ[C]. Consider:

* **Exact test**: |C|≤Raw(supp(C)) for every nonempty directed B-clique C.
* **Full test**: |{x∈C:σ(x)∈T}|≤Raw(T) for every directed B-clique C (including empty) and every nonempty admissible integer-age support T of size at most ell−1.

**Exact → full:** Given C,T, let D be the restriction of C to vertices labelled in T. D is itself a directed clique and D⊆C. If D is empty, the full inequality is immediate. Otherwise supp(D)⊆T; apply the exact test to D and then raw monotonicity. The result is exactly the T-count of C. This direction does not need K_ell-freeness.

**Full → exact:** For any nonempty B-clique C, its size is <ell by the genuine finite K_ell-free check, hence supp(C) is an admissible integer-age support: it is nonempty and has size ≤|C|≤ell−1. Take T=supp(C). Every vertex of C survives the T-restriction, so the full test gives |C|≤Raw(supp(C)). Without K_ell-freeness, this choice of T might not belong to the restricted age domain; the hypothesis must NOT be omitted.

## Canonical form under the verified Track F source/target hypotheses

Write R_s(T), R_t(T) for the genuine old-neighbour clique-capacity raw functions restricted to IntegerGraphSupport(d,ell). Define G_s=integerGraphAgeCanonical(R_s), G_t=integerGraphAgeCanonical(R_t).

Assume the precise hypotheses from PR #383: actual source and target Henson finite types at common respective levels, induced injective source→target embedding (not order-preserving), target K_ell-freeness, rank-large ACTUAL source coding fibres for each target type, and image-below-cutoff for every positive old source neighbour. Assume B symmetric, and additionally finite B K_ell-free on [0,N).

Then the following TWO complete all-support clique tests are logically equivalent:

    ∀ C⊆[0,N), clique_B(C), ∀ T∈IntegerGraphSupport(d,ell),
        count_σ(C,T) ≤ G_s(T)
      ↔
    ∀ C⊆[0,N), clique_B(C), ∀ T∈IntegerGraphSupport(d,ell),
        count_σ(C,T) ≤ G_t(T).

Proof: use verified finite-clique integer-canonicalization equivalence separately for the two genuine raw functions, converting G_s- and G_t-tests into their respective full raw-support systems. Use the bridge just proved to convert each full raw system into its exact-support form. Apply merged PR #383 to the exact forms, then reverse the conversions. This supplies exactly the same normalized integer-witness age criterion on both sides for each fixed finite B, not a claim that R_s=R_t numerically.

## Hostile audit and nonclaims

1. **Check the support quantifiers.** PR #383 tests just C.image σ, but the integer canonicalizer tests arbitrary admissible T, including unused sorts. We must not skip the restriction-to-T argument.
2. **Check truncated subtraction.** The raw monotonicity direction is increasing with support, because common old pools *decrease* and clique capacities decrease. It is NOT antitone.
3. **Check the empty restricted clique.** Its cardinality is zero, so no appeal to the nonempty exact-support theorem is possible or needed.
4. **Check nonempty supports.** A nonempty C always has a nonempty image under total σ. Conversely, every T belongs to the explicit nonempty IntegerGraphSupport domain.
5. **Check support size.** The full→exact direction requires |supp(C)|≤ell−1. This comes from actual K_ell-free finite B, not merely from formal cardinality of Fin(d).
6. **Check both directed adjacency orientations.** B-clique means IsDirectedCliqueOn B, and restriction preserves both directions. Source→target e preserves directed bits off diagonal.
7. **No assumption that σ is injective.** Several vertices may have the same sort; filtering by T counts *vertices*, not distinct labels.
8. **Do not equate canonical and raw numerically.** The verified integer universal-property theorem provides equality of feasible normalized vector systems, not equality of the individual raw bounds.
9. **No positive age assertion.** We only use the numerical canonicalizer. It is not necessary here to claim G_s or G_t is a genuine positive age absent the separate eligibility hypotheses.
10. **No arbitrary finite-weight realization assumption.** We work with actual abstract finite B-cliques and the already verified equivalence of all-support clique tests with the canonicalizer. We do not assume a fixed physical target fibre realizes every normalized weight vector.
11. **No physical target-front construction.** All compatible rank-large target fibres and the cutoff remain explicit hypotheses, as in PR #383. This proof does not synchronize them.
12. **The K_ell-free assumption concerns B.** It is independent of the target Henson forbidden-family condition and must not be silently derived from that.
13. **No full Kpt E/parameter or B3 equivalence.** Only ordinary L-clique feasibility and integer-witness graph-age tests are compared.
14. **No automatic diary persistence.** Equality of these tests for a fixed compatible tuple does not provide a resolved embedding that persists through an arbitrary self-copy.
15. **No exact big Ramsey count.** The lower-bound unavoidability argument remains open.
16. **Manuscript policy.** Frozen black proof text must not be edited. If this bridge is reused in the olive synchronization argument, mark the dependence on actual simultaneous compatible fibres; a black-text fix can be recorded as a TODO without changing the prose.

## Validation and promotion gate

Produce three named source-checks (raw support monotonicity; full↔exact raw finite-clique test; complete canonical source↔target all-support test), with a dedicated exact-head Lake build and strict standard-only transitive axiom report. Keep the branch DRAFT until the CI is green. Any standalone algebraic equivalence may then be promoted; the global diary lower-bound theorem must remain unvalidated.