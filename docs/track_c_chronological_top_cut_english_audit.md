# Track C — the actual chronological cut bounds ALL inherited H+ Kpt seeds

**14 November 2026 — English proof and hostile audit BEFORE Lean.**
Stacked on the mathematically repaired PR #165, which now seeds **new original Kpt nodes only**, never the full prefix pool; do NOT use the superseded all-prefix seed definition. This PR is a concrete numerical-geometry repair, not a global resolved-copy claim.

## Problem in the bounded new-root theorem

The strengthened PR #165 theorem needs an explicit inequality `N≤top` to show that *all* old Kpt seeds and meet/parameter closure nodes lie at/below the new top free cut. It is NOT automatic if the old numerical cutoff N is chosen as `hPosition k b 0`, because for the first new block j=b the true top E-free cut is

`hPosition k (b-1) k+1 = hPosition k b 0 -1`.

Thus the naïve old prefix ending precisely at the first new block would overshoot the new root's E-free level by one! The appropriate complete numeric old prefix ends at

```
N := hPosition k (b-1) k +1,
```

the coordinate immediately after the LAST real top-generation original of old base block b−1. For b>0 this includes **all genuine real-generation copies** from base blocks i<b, but excludes the trailing dummy/gap coordinate before the next base block.

## C44. Full real old-block coverage by the tight cutoff

For any `k,b,i,q` with `0<b`, `i<b`, `q≤k`, we have

`hPosition k i q < N`.

**Proof:** if i=b-1, the numerical position is at most the last old top `hPosition k (b-1) k`, since q≤k. If i<b-1, block order `hPosition_lt_of_block_lt` places every generation-q position strictly before the last old top. No numerical H real original from old blocks is lost. The trailing odd fake coordinate, however, is deliberately omitted: full physical old sources depend only on their actual free cuts, not on physically retaining every irrelevant odd target.

## C45. Correct chronological carrier and free-level inequalities

Fix k, old block count b>0 and new block j≥b. Let
`N=hPosition k (b-1) k+1`. Suppose the new top position is physically in the new carrier, `hPosition k j k<M`.

Then
```
N ≤ hPosition k b 0,          -- before NEW base block
N ≤ hPosition k (j-1) k+1,   -- at/below NEW true top E free cut
N ≤ M.                         -- old H+ carrier sits in new one
```

The first follows from block order b−1<b; the second from the
monotonicity of the coordinate polynomial in the original block
index b−1≤j−1; the third from block order b−1<j and in-carrier new
target. No assumption of old original graph's auxiliary E is used.
The source and generation parameter k remain fixed.

## C46. Construct a fully bounded physical H+ run from a chronological root without hNTop premise

Let K,L be base age-test models with the SAME full directed binary,
unary and diagonal columns on all old original indices <b; let
old finite physical numerical H+ carrier be the NATURAL N above,
and the new carrier M contain the true new top root
w=`hPosition k j k`, k>0, j≥b>0. Assume genuine avoided-family
certificates for the two actual finite H+ models, and an old Kpt
seed set X with genuine old original-prefix root pool U⊆Fin N.

Define the corrected explicit next seed Y of PR #165:

```
Y = closure (admissibleKptSTree family) I X
     ∪ {B.kptOriginal w},
```

where B=`finiteNumericH L k M`. Note that the new-root proper
prefix chain is NOT preinserted as a set of initial seeds.

Then **without any user-supplied `N≤top`**, the true generation E
formula and C45 discharge all hypotheses of the strengthened PR
#165 theorem. Consequently:

- Y has real physical original-prefix witnesses,
- a genuine AlgorithmRun R on Y is CONSTRUCTED,
- Y contains a true top-level Kpt original,
- the COMPLETE final meet+parameter closure has a finite injective
  name index and actual Boolean pre-cut active masks,
- **all of Y** lies at/below the true new top free level
  `top=hPosition k (j-1) k+1`.

This does NOT imply that the algorithm selects only the prescribed
macrodiary levels; genuine extra I1/I2/I3 auxiliary microevents
remain possible. Its event count is NOT proved uniformly bounded.

## Hostile audit

1. This argument applies only for b>0; the very first stage b=0 requires its own initialization.
2. The new root j must satisfy j≥b, not merely j>0.
3. The construction must seed only the genuine new original Kpt node(s), not the entire prefix pool (which would force all I1 levels).
4. `N=hPosition k (b-1) k+1` includes all real copies with i<b,q≤k; do not confuse it with the start of block b, which is N+1.
5. The actual free cut is `hPosition k (j-1) k+1`, not the physical position `hPosition k j k`.
6. k>0, j>0 and new top target in carrier are needed for the E-free-level formula.
7. Base K→L old column equality in both directed orientations plus unary and diagonal data remains essential.
8. Both finite physical H+ models must avoid the forbidden family; this is not inferred from a stand-alone universal graph age with no old-prefix certificate.
9. Old inherited nodes are actual admissible Kpt nodes; a selected-L graph shadow is insufficient.
10. The verified successor-tree closure level bound applies to meets AND generated parameters, not just original seed vertices.
11. Auxiliary E on odd fake source coordinates remains literal in the original types; omitting a trailing fake TARGET does not erase an existing old E source bit.
12. The finite `params` index is per constructed run, not a common index across different occurrence embeddings.
13. K4 actual cuts 10/22 remain possible nonboring microevents.
14. No infinite coherent resolved-copy schedule, common labelled inverse-source orbit or unconditional BRD characterization is proved.
15. This is a concrete chronological inequality/property theorem, not an assertion that arbitrary new Henson backward columns have been constructed.

## Lean acceptance

Add a new module `Kk/NumericHChronologicalTopCut.lean`, with three
named theorem endpoints (old-generation coverage, chronological triple
bounds, fully bounded repaired physical new-root AlgorithmRun). All
theorems require a direct exact-head Lean build and strict standard-only
axiom report, plus separate full-project CI. No changes to protected
manuscript, central aggregator or shared validation marks.
