# Upper characterisation continuation: checked scope and remaining obligations

## Published proof snapshot

The six new modules and four repaired interfaces were first published at
`7337955d37f386d2ef0e7c27abb96b234e892bd3` in
[PR #512](https://github.com/janhubicka/lean-kk/pull/512).
Their English proofs and independent reviews were committed before implementation.

The [focused workflow](https://github.com/janhubicka/lean-kk/actions/runs/45186291201),
job `137732646828`, built all ten targets and passed the strict
`scripts/check_axioms_upper_continuation.lean` gate: **25 exact transitive-axiom
reports**, with only `propext`, `Classical.choice`, and `Quot.sound` allowed.
The 25 names comprise 16 new declarations, all eight repaired declarations,
and the existing isolated-dummy TOP-seed endpoint used by the manuscript.

The initial root aggregation placed imports after module documentation.
Commit `7dfcc2a5a0d9d2c9c4e390d6160316526fa2c15c` corrected that ordering
without changing any proof module or the focused audit. The independent
[root workflow](https://github.com/janhubicka/lean-kk/actions/runs/45187467235)
then completed both `lake build` and its strict central gate successfully.
The central audit requests **1,132 exact reports**. The focused gate also
passed again at that integration commit in
[run 45187467030](https://github.com/janhubicka/lean-kk/actions/runs/45187467030).
These are hosted kernel checks of the published sources; they are not inferred
from source-token scans or from the interrupted local dependency warm-up.

## Canonical address repair

The literal address is `p(j,m) = 2*(k+1)*j + 2*m`. Unrestricted natural
generations admit aliases, including `p(j+1,0) = p(j,k+1)` and
`p(j+1,k) = p(j,2*k+1)`. Therefore the old root and Plan contracts could force
conflicting roles for valid earlier bases. This obstructed the intended
application; it was not a counterexample to the old implications under their
stated stronger hypotheses.

All affected contracts now require the canonical generation bound `m ≤ k`,
including TOP. Physical-neighbour decoders already return that bound, and
every affected call site forwards it. The regression module proves the
overflow aliases and concrete bounded-role assignments that contradict their
unbounded versions.

## New proved implications

| Module | Checked mathematical content |
| --- | --- |
| `EqualCutFullType` | Genuine eligibility, complete old type equality, symmetry, and equality of the ordinary cut bit determine the complete next L+/E type. All six next-column fields are retained. |
| `ResolvedQBlockSeparation` | Across an omitted non-dummy base, later retained auxiliary originals have zero old base column, assuming block convexity modulo inserted dummies. |
| `RealPositionGenerationAliases` | Two universal numerical aliases and two concrete root/Plan contract regressions. |
| `PositiveGenerationStageCoherence` | On every eligible actual stage original, the ordinary bit at a lower generation equals its generation-zero bit. For `0 < g < k`, this yields complete old-to-next coherence. |
| `StageCoherenceStructural` | Whole-stage coherence and genuine source/seed hypotheses exclude I1 terminals and I2 meets, including generated parameters, proper meets, and self-meet boundary cases. |
| `PositiveGenerationStructural` | The structural bundle applies to the literal `Run.I(c+1)` stage and the cap/TOP-prefix seed family. A separate nonselection implication retains the actual chosen Marked corrected-B3 verdict. |

The positive-generation argument uses `q = p(b,0) < c = p(b,g)`. A positive
ordinary bit at either tested coordinate yields a canonical later real name;
the bounded role classification forces that name to selected TOP. Both
generation gates are then open, so the Boolean bits agree, including false
values. Complete old types already contain the q-coordinate. No age-neutrality
or selected-only source replacement is used for this argument.

The structural transport first obtains original-meet witnesses from the full
closure normal form. At a positive even real cut, positive-free-level parity
turns a weak level bound into genuine eligibility. It separately proves no-I1
before using strict-fork exclusion to prove no-I2. Thus an endpoint cannot
escape through the self-meet case.

## Application checks and genuine remaining gaps

The independently reviewed
`2026-11-23-positive-stage-nonvacuity-and-zero-boundary.md` exhibits a nonempty
physical stage with positive neighbours satisfying the bounded contracts.
It also shows why those hypotheses alone cannot establish generation-zero
coherence against an eligible zero-old cap. That example is a mathematical
source review, not an additional kernel-checked theorem or a claimed exact
AlgorithmRun realization.

The following construction obligations remain open:

1. Realize the actual resolved Q, retained roles, and Plan, and prove the
   descending inclusion for the genuine current AlgorithmRun stage.
2. At generation zero, establish neutrality and no-splitting for every
   eligible selected TOP representative, together with separation from
   eligible zero-old root and retained auxiliary originals.
3. Verify the planned odd free-cut closure and the actual chosen corrected-B3
   verdicts at the remaining omitted cuts.
4. Identify the common labelled full source and its orbit, then finish the
   global upper canonisation argument.

These checked conditional implications do not establish the complete
characterisation theorem or an ordinary big Ramsey degree equality.

## Recovery limitation

The previous local 20-module / 218-report continuation was unavailable after
workspace restoration. Its exact unpublished commit objects were not found
locally or on GitHub. This continuation starts from published main
`0fcac8624ef0328ff4b885b8945e682d480d8669`, reconstructs the two upper lemmas
whose complete source was visible, and adds the independently reviewed new
work above. It does not claim to restore or freshly verify the unavailable
ordinary lower-bound implementation. Draft PR #504 remains separate.
