# Track G — arbitrary finite-run factorization is NOT boring compression

17 November 2026. English proof and adversarial audit, before Lean.

## Mathematical correction and theorem A

Let H be a genuine SMTree and R an actual AlgorithmRun H X top.
Fix any low <= high <= top, with NO condition on interesting levels.
Then exactly one total D:MMap H satisfies

    R.F low = MMap.comp H (R.F high) D.

Proof. Descend from high to low. At high, take the identity.
At an interesting stage i the actual step law says F(i)=F(i+1),
so retain the factor already constructed for [i+1,high].
At a boring stage i, noninteresting_step supplies a genuine
skip-only monoid map Di with F(i)=F(i+1) composed with Di.
If the previous factor is E, choose E composed with Di.
Closure under composition is built into MMap.comp, and actual
pointwise composition is associative by MMap.ext_apply.
This constructs a genuine TOTAL factor on any finite interval.
Injective left-cancellation of the actual high-endpoint map,
already verified as Kk.kpt_MMap_comp_left_cancel (G309), proves
that D is unique. Crucially, no boring hypothesis is used.

## Theorem B — exact criterion for constant selected levels

For the same true run and interval,

    R.I low = R.I high
       iff every i with low <= i < high is genuinely boring on
       the actual complete closure of (R.I (i+1)) and X.

Backward implication: the verified G305 all-boring block theorem.
Forward implication: suppose i in the interval were interesting.
The interesting_step law places i in R.I i. By the already verified
AlgorithmRun.I_eq_final_tail_of_run, i belongs to R.I 0 and,
since low <= i, also to R.I low. By the alleged endpoint equality,
i belongs to R.I high. But the already verified I_mem_bounds
forces high <= i, contradicting i < high.

Thus the selected-set equality, not existence of a monoid factor,
is exactly what identifies an all-boring block.

## Hostile checks

1. This is for one genuine AlgorithmRun, not two diary occurrences.
2. No one-level pullback (E1), top seed nonemptiness or source bound
   is introduced: it uses only the verified actual-run interface.
3. At interesting stages use the actual F equality, not a fiction
   that interesting levels have skip-only maps.
4. At boring stages use the actual full parameter-closed test,
   not selected-front ordinary graph ages.
5. Composition order is E after Di, matching F_i=F_high o E o Di.
6. Total MMap.ext_apply is needed for associativity; the graph-age
   quotient is insufficient for unique cancellation.
7. The empty block has a unique identity factor by injectivity.
8. An interesting-only block has D=id despite selected I changing;
   therefore factor existence does not diagnose boringness.
9. All-boring blocks can have nontrivial D, including long skip data.
10. The new theorem says nothing about the factor's label complexity.
11. K4 selected microcuts 10 and 22 are compatible with theorem A;
    they prevent theorem B's boring conclusion on crossing intervals.
12. The proof of theorem B uses genuine final-tail invariance;
    equality of only two selected-front graph ages is inadequate.
13. No monotone/canonical cut-coordinate map between different
    occurrences is supplied.
14. No uniform bound on the number or lengths of physical bad-cut
    intervals follows; their single-node witnesses can recur.
15. The full dependent L+/E source-orbit comparison, corrected
    (B3)-loss equivalence, resolved infinite copy and unavoidable
    independent lower colouring remain pending.

## Validation protocol

Commit this English proof first, followed by a standalone Lean file
importing the already checked G309 factor-cancellation module.
Directly compile that exact source head and check two exact qualified
#print axioms declarations with the strict parser negative self-test.
The main Kk.lean importer is left unchanged until independent CI.
Neither the frozen black manuscript nor its validation marks are
touched until a passing source-specific gate is available.
