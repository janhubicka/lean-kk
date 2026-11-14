# Track E — actual AlgorithmRun physical-source stability under finite H+ carrier growth

**14 November 2026. English proof and adversarial review before Lean.**

Stacked on Track C [PR #145](https://github.com/janhubicka/lean-kk/pull/145) and [#140](https://github.com/janhubicka/lean-kk/pull/140), whose exact-head Lean source gates passed. This is a separate Track E comparison result; it does not modify either prerequisite C PR. Ultimate parent: manuscript [KK Track E #27](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/issues/27).

## The genuine physical case covered

Fix the *same* age-test base `K`, generation k and numerical H+ scaffolds `A_N=finiteNumericH K k N`, `A_M=finiteNumericH K k M` with `N≤M`. Both ordinary-L structures genuinely avoid a fixed normalized forbidden family. Fix actual root-original pool U⊆Fin N and a fixed seed set X of genuine Kpt nodes represented by prefixes of A_N's old physical originals, and assume the **SAME Kpt source set X**, embedded literally in the same `admissibleKptSTree`, is used for both runs.

Take TWO genuine runs
`R : AlgorithmRun (normalizedKptSMTree family) X top` and
`S : AlgorithmRun (normalizedKptSMTree family) X top`,
with independent choices of skipping shape maps and possibly independent physical ambient-original names. We are NOT assuming `R.I=S.I` or `R.F=S.F`.

**Result A — all selected levels coincide.** The already verified generic `AlgorithmRun.I_eq` implies `R.I i=S.I i` for every i≤top, since both start at `{top}` and make the true semantic interestingness decisions for the SAME Kpt seed set. No new E1 hypothesis is needed and neither the physical carrier N nor the chosen maps enter the conclusion.

**Result B — physical old+upper FULL L+ source and corrected B3 coincide at every no-(I2) cut.** Fix c<top and assume no actual competing I2 meet at cut c in the full source `Z_R=closure (R.I(c+1)) X`. By Result A, the corresponding true source `Z_S=closure (S.I(c+1)) X` is LITERALLY the same Kpt set, and hence its no-I2 property is derived (not independently assumed).

Track C PR #140 proves the actual old numerical-H+ Kpt originals, complete E columns and all old/upper L+ types are physically unchanged under `Fin.castLE`. It transports the root pool U and the complete meet/parameter source into the enlarged H+. The exact full-closure comparison from PR #145 then proves, for `F_N=closureSelectedBoringData(A_N,Fin N,Z_R,c)` and `F_M=closureSelectedBoringData(A_M,Fin M,Z_S,c)`, ALL THREE:
`F_N.source = F_M.source`,
`∀T∈F_N.source, F_N.target T=F_M.target T` (COMPLETE dependent L+, including E), and
`F_N.CorrectedB3 family ↔ F_M.CorrectedB3 family`.

This is now a theorem about **two ACTUAL AlgorithmRuns**, not merely two arbitrarily chosen selected-level sets I. It proves that enlarging a finite numerical-H+ scaffold cannot perturb any part of a fixed true run's complete chosen source/B3 diagram, PROVIDED THE underlying seeds X, base K, generation k remain fixed.

### Hostile audit

1. **Fixed seed set is crucial.** The resolved-copy recursion may add new roots/selected copies; the resulting X changes. The theorem does NOT say these larger sources share the same selected levels, physical crossing relations, or B3 profile.
2. **Fixed K and k are crucial.** PR #140's actual numerical-H prefix identification uses both; changing generation alters the H source positions and E free cuts. Do not treat arbitrary different diary occurrences as prefix extensions.
3. **Exact full source, not selected shadow.** All closure meet and parameter nodes are included; auxiliary odd fake E predecessor bits are retained in full Kpt types.
4. **No-(I2) only for functional B3.** At a genuine I2 fork, the canonical physical crossing RELATION is still stable because the literal source is the same, but no single-valued `F.target` is claimed to cover all forks. The result therefore limits the prescribed B3 graph statement to non-I2 cuts, without deleting those structural events.
5. **No uniform bound.** The physical carriers N and M are arbitrary finite sizes; this yields no constant finite diary carrier independent of the resolved target.
6. **No labelled orbit.** Even equal selected level sets and full prescribed source graphs of two runs with identical seed sets do not give a common outgoing labelled inverse-source orbit ACROSS DIFFERENT seed sets. `R.F` and `S.F` may be different monoid maps.
7. **Outside-source `F.target` is meaningless.** Equality is only on the actual common source domain.
8. **B3 remains a finite L-only age test.** Equality of complete physical sources does NOT create an E relation on separate forbidden-copy age witnesses.
9. **Cut range.** For intended physical applications it is natural to require `cut<top` and to keep the run horizon below an actual stage bound. The staged theorem compares only true scan cuts, not arbitrary artificial target positions after inserting boring gaps.
10. **No inference from unrefined diary equality.** This theorem gives a defensible physical stability result for enlargement of a single source, not a proof of the cross-occurrence characterisation or BRD numbers.

### Exact Lean target

Define `numericH_two_actual_runs_prefix_full_source_and_B3_stable`: simultaneously construct equality of all selected level sets and, at every scanned cut satisfying actual full-source no-I2, equality of the complete old→upper prescribed graphs and corrected B3, with `Z_N` taken from the FIRST genuine run and `Z_M` from the SECOND. The actual physical H+ avoidance/prefix assumptions are displayed. Do not introduce `sorryAx` or unproved new axioms. Run isolated compilation plus exact named transitive-axiom checks, then independent full build. Keep PR stacked/draft until prerequisite C #145/#140 are merged and Track G integrates.

This closes a **same-physical-source prefix stability** gap; the remaining genuinely difficult theorem is a same-*diary* comparison of DIFFERENT resolved sources with common normalized source coordinates, selected-vertex labels and dependent parameters.