> **SUPERSEDED seed formula (14 November).** This English boundedness argument originally included `ambientPrefixPool B {w}` among the new initial seeds, forcing every numerical level to be I1. The separate [overgeneration-repair audit](track_c_new_root_overgeneration_repair_english_audit.md) explains why this is unacceptable and replaces the new seed component by the **singleton set of actual Kpt original nodes**. The bound on the ENTIRE corrected Y still follows under the same explicit `N≤top` hypothesis.\n\n# Track C repair: genuine top seed does NOT automatically bound all seeds

**14 November 2026 — English-first adversarial correction before the Lean patch.**
PR #165's original three theorem endpoints were verified on the isolated module gate with exact standard-only axioms. An additional mathematical hypothesis is needed before using the result in the successor-tree *bounded envelope* theorem: `canonicalAlgorithmRun` is defined at arbitrary height `top`, even if some seed has level ABOVE that height. Existence of one top-level seed does not imply all seeds are bounded.

## Correct strengthening

Keep the physical old-base-extension assumptions of PR #165, including fixed generation k and old numerical N≤hPosition k b 0 and old actual Kpt seed set X with original pool U.

Choose a **genuine top-generation new root** `w=hPosition k j k<M` with k>0,j>0 and top
`t=hPosition k (j-1) k+1` determined by its actual incoming E-column. Add the meaningful chronological bound

```
N ≤ t .
```

Let `Y = closure (admissibleKptSTree family) I X ∪ ambientPrefixPool family B hAvoidB {w}` be the explicit complete next-seed family. Then the already verified PR #165 theorem gives an actual run R, genuine top seed and finite exact source records; **additionally**

```
Y ⊆ SMTree.Envelope.levelLe t .
```

### English proof

For any old z∈X represented below an actual original Kpt node `A.kptOriginal v` with v<N, monotonicity of levels gives
`lev z ≤ A.freeLevel(v) ≤ v < N ≤ t`.
Hence `X⊆levelLe(t)`.

The verified successor-tree `closure_subset_levelLe` (its proof includes both meet and selected-parameter closure) gives
`closure I X ⊆ levelLe(t)`.

For any z∈ambientPrefixPool B {w}, choose its original witness `B.kptOriginal w`. Its LevelTree level is the **actual** E-free cut t, by `finiteNumericH_top_freeLevel_exact`; therefore `lev z ≤ t`. This is true for all real/admissible parameters, not merely selected original vertices.

Thus every z in their union Y has lev z≤t. Crucially no upper bound is assumed on an arbitrary supplementary Y. This is an honest genuine original-root/source construction with no omitted auxiliary Kpt node.

### Why N≤t is required

Even when a new root w has level t, the inherited old closure may contain nodes above t; then a run at t does not scan those nodes in the intended descending induction. One cannot infer the full bounded-envelope invariant from top seed existence alone. The explicit N≤t guard is sufficient, and for a chronologically chosen new top original sufficiently far after old blocks it can be checked arithmetically. This theorem does NOT claim that a fixed j automatically provides that inequality.

## Hostile checks

1. No replacing `lev original` by its numeric physical address; use E-free level ≤v.
2. Old X is a subset of genuine original-prefix pool, not arbitrary Kpt nodes.
3. The meet-and-parameter closure cannot raise LevelTree height by the verified `closure_subset_levelLe` theorem; no false finite-graph projection.
4. The new singleton prefix pool consists of genuine Kpt predecessors of the exact new top original w, all ≤t.
5. `N≤t` must be explicit and checked; it is NOT implied merely by k>0,j>0 and old N≤blockStart(b) without a relation between b and j.
6. The result is for the ENTIRE Y seed set, not only selected original endpoints.
7. The true top E free cut formula needs k>0,j>0 and in-carrier target.
8. This does not bound the *number* of Kpt nodes uniformly in N; merely all node levels ≤t.
9. Having `Y⊆levelLe(t)` enables legitimate use of bounded-envelope successor-tree arguments, but does not establish exact canonical resolved diary events.
10. New original forbidden-family avoidance and mixed old-column clique budgets are still separate physical obligations.
11. No cross-occurrence labelled source equality, monoid orbit or BRD characterization is asserted.

## Lean target

Append one **FOURTH** named endpoint
`finiteNumericH_baseExtension_actual_top_root_run_bounded`
in the Track C PR #165 module, referring to the previous verified
top-run existence theorem and proving `Y⊆levelLe(t)`.
Rerun isolated direct module build with EXACTLY FOUR named
standard-only transitive-axiom reports and the full-project gate
at the new exact head. Do not modify `Kk.lean` or protected text.
