# Track D — a base-graph certificate sufficient for full corrected B3 at a non-top real cut
16 November 2026. English-first proof and adversarial audit BEFORE Lean.

## Why this is useful

The small-independent upper proof currently claims that at certain omitted real cuts, only selected TOP originals can be positive ordinary-L future neighbours. The correct finite object to classify is the **genuine full closure-selected original-name pool**, including Kpt-generated auxiliary parameters, whose chosen next-cut ordinary-L types enter the corrected-(B3) test. Graph-age equality on the selected active shadow cannot substitute for this.

Two independent verified modules are now available:
- `Kk.PhysicalLowerRealCutNeighbour.finiteNumericH_eligible_lower_cut_neighbour_is_higher`: at physical cut `c=hPosition k idx g` with `g<k`, every actual free-cut-eligible positive physical name lies at `hPosition k j m` for `idx<j`, `g<m<=k`, and actual base graph `E(idx,j)=true`.
- `Kk.B3CutVisibleNoNonempty.henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty`: if a represented Marked source contains EVERY genuine cut-eligible positive Full name, actual no-(I2) holds on the SAME Kpt closure, and Marked's **chosen complete upper-L type** profile passes corrected B3, then Full corrected B3 passes. An independently nonempty Marked source is NOT required.

## Exact theorem (one physical cut, no AlgorithmRun needed)

Let `ell>=2`, `ell<=k+1`, E symmetric/loop-free/K_ell-free, A the actual finite numerical H(E,k,N). Fix a physical real cut `c=hPosition k idx g < N` with `g<k`, one finite `original : Fin M→Fin N` pool, a genuine Kpt closure Z, and arbitrary predicates Full/Marked on that pool. Assume:
1. Every Marked name represents an actual Z closure node crossing c, in the exact sense of `closureSelectedOriginal`.
2. Z has no (I2) competing meet at c.
3. **Base-block coverage, stated only in actual original graph terms**: whenever Full(v) and `original(v)` has physical address `hPosition k j m`, with `idx<j`, `g<m<=k` and `E(idx,j)=true`, then Marked(v). This is uniform over ALL eligible/auxiliary full names and is NOT just a selected active branch-age equality.
4. The full selected-stage prescribed function constructed on the Marked original pool passes corrected (B3).

Then the full selected-stage prescribed function constructed on Full passes corrected (B3).

## English proof

Let v be an arbitrary Full selected name which is eligible at cut c and has positive actual ordinary-L edge `L(c,original(v))=true`. Use the exact higher-generation physical positive-neighbour theorem. It says v is a later-base higher-generation physical address with E(idx,j)=true, so assumption (3) makes v Marked.

Thus every cut-eligible positive Full name is Marked. Assumptions (1),(2),(4), together with the already verified no-marked-nonemptiness no-(I2) finite transfer, give Full corrected (B3). This is one exact line of composition after the physical base classification. No arbitrary age-test upper-upper edges or auxiliary E are assigned physically; (1)--(2) guarantee source-fibre coherence of COMPLETE chosen upper-L types from actual represented Marked originals.

### Contrapositive

If Full corrected B3 fails while Marked is genuinely represented and corrected-B3-good and no-(I2) holds, then at least one FULL, unmarked cut-eligible positive original must lie at a strictly later base j and higher generation m, with base E(idx,j)=true. The stricter *same forbidden clique* witness is independently formalized in PR #246 for true selected nonstructural I3, but is NOT a premise of this theorem.

## Fifteen adversarial checks

1. The original graph E is physical graph adjacency, NOT numerical H+ auxiliary E. The theorem uses E(idx,j) only as the base ordinary-L bit.
2. The original name v may be a parameter-generated full closure name, not an active selected diary branch. Assumption (3) quantifies over the FULL pool.
3. The physical cut `hPosition k idx g` with `g<k` is a GENUINE numerical coordinate, not arbitrary compressed/successor reindexing.
4. Exactly `g<m` and `idx<j` are guaranteed by positivity and free eligibility, but the equivalence depends on physical numeric ordering and absence of exceptional top/top tie. No top cut version.
5. No marked source nonemptiness is assumed: the verified strengthened transfer derives it in any Full failure case.
6. No-(I2) belongs to ONE specific Z and ONE exact source name pool. Do not replace it with a no-fork test on selected branches.
7. Marked representation in Z is genuinely required to deduce the chosen output agrees with every marked real next full L+ source fibre. Merely `Marked v` does not imply the chosen function selected v.
8. The Marked corrected B3 test is an ASSUMPTION; selected graph-age equality does not prove it over the fixed old complete L+ prefix.
9. The conclusion is the FULL chosen corrected-B3 test, not whole boringness or absence of I1/I2.
10. Do not drop `cut < N`, free level eligibility, or source original actual Fin N physical membership.
11. The normalized forbidden-family hypotheses are explicit and include forbidden asymmetry/singletons as needed; do not generalize to arbitrary relational patterns without proof.
12. No source support-diary orbit, original-Q independent history, or universally bounded BRD follows.
13. Actual base-block coverage is precisely the missing geometric property to be verified from the retained small-independent Q construction; this theorem makes that dependence visible.
14. The reverse implication (full B3 -> base block coverage) is NOT asserted; full B3 might hold despite missing names. The source condition is sufficient, not necessary.
15. A separate future actual-AlgorithmRun instantiation must connect the complete Run.I(c+1) closure Z and Run.I0 original pool. This theorem does not postulate that all ambient originals are Full.

## Lean plan

Implement in `Kk/B3LowerRealBaseCoverage.lean`, import the two checked modules and mathlib tactic, prove `henson_fullB3_of_lower_real_base_covered_marked_source` with EXACT explicit assumptions. Its Lean proof should introduce a Full positive cut original, apply `finiteNumericH_eligible_lower_cut_neighbour_is_higher`, derive the Marked inclusion from hBaseCovered, and invoke `henson_fullB3_of_no_i2_marked_closure_cut_neighbours_no_nonempty`. Register in dedicated exact-head strict transitive-axiom audit. This is intentionally NOT a proof of the missing Q-schedule base coverage itself.

This proof can be used as the precise even-cut B3 application interface in the manuscript olive text once kernel-checked.
