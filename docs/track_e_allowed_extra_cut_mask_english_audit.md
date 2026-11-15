# Track E — allow listed diary microcuts, exclude every other old-range novelty

**15 November 2026. English proof and adversarial checklist BEFORE Lean.**
Follow-on to the existing kernel-checked cross-height physical novelty theorem
(PR #203) and the stacked physical finite-index application (PR #206).
Do not mark the diary upper bound green.

## E51. The *relative* no-unplanned-cut criterion

Fix an actual common admissible Kpt tree, true Kpt seed sets `X⊆Y`,
genuine AlgorithmRuns `R` and `Q` with scan tops `oldTop≤newTop`, and a
REAL seed `x∈X` at the old top. Fix an explicit set
`Allowed ⊆ Nat` of permitted extra source-coordinate cuts. Its intended
application is the set of *planned resolved diary microevents*, including
genuine auxiliary E and K4 cuts when present, NOT just the macrodiary levels.

For each `c<oldTop` which is **old-boring**
(`c∉R.I c`) and **not allowed** (`c∉Allowed`), assume the following two
one-sided physical checks on the ACTUAL parameter-closed pre-cut sources
`Zold(c) = closure_(R.I(c+1)) X` and
`Znew(c) = closure_(Q.I(c+1)) Y`:

1. Any level-c terminal witness in the new Kpt source is witnessed
   by *some* level-c terminal node in the old source.
2. The canonical complete old/upper dependent L+ crossing relation of
   the new source at c is contained in that of the old source, including
   auxiliary E, negative L bits and ALL crossing pairs at I2 forks.

Equivalently, require `NewRootNoNoveltyAtCut Zold(c) Znew(c) c` **only**
at off-plan old-boring cuts, rather than at every old-range cut.

**Pointwise conclusion.** Every NEW selected cut `c<oldTop` absent from
the old run MUST belong to `Allowed`:

`c∈Q.I c ∧ c∉R.I c → c∈Allowed`.

Proof: suppose an extra selected c is unallowed. The established
cross-height novelty theorem (requiring the real top seed and literal
X⊆Y) produces a new actual terminal node at c OR a new complete
old/upper physical crossing pair absent from Zold(c). The first case and
the off-plan terminal coverage force old I1 interestingness and hence
`c∈R.I c`, contradiction. The second case contradicts the off-plan
crossing relation inclusion.

**Stagewise conclusion.** For each `i≤oldTop`,

`R.I i ⊆ Q.I i`

and

`{q∈Q.I i : q≤oldTop} ⊆ R.I i ∪ {q∈Allowed : i≤q}`.

The first inclusion is real-top cross-height seed monotonicity. For
the second, let `q∈Q.I i` with `q≤oldTop` but `q∉R.I i`.
Actual final-tail identities give `i≤q` and `q∈Q.I q`.
If `q=oldTop`, the genuine old run always contains its own top
at EVERY stage i≤oldTop; contradiction. Thus q<oldTop.
Again by final-tail, `q∉R.I q` (otherwise it would belong
to `R.I i`). The pointwise conclusion forces q∈Allowed.

In particular, `Allowed=∅` recovers the previous old-range equality
under the *weaker* no-novelty hypotheses checked only at old-boring
cuts. For finite `Allowed`, there can be at most `|Allowed|`
extra old-range selected levels, but exact cardinality still needs
the expected microevents to be realized.

## Why this matters for the resolved diaries

Previously, the simple finite coverage criterion asked for no new
crossings even at ALREADY-INTERESTING old cuts. That condition is
unnecessarily strong. The new relative criterion asks only that no
UNPLANNED old-boring cut acquires a novel monoid-level obstruction.
It can record and retain the actual auxiliary cuts 10/22 in the K4 q2
examples rather than forcing all cuts to be boring or throwing them away.

The theorem is a **sufficiency test**, not an assertion that the diary
automatically supplies the two tests. To finish Track E, derive their
true finite-index / physical source versions FROM the corrected
resolved diary and prove a common labelled inverse-source orbit.
Different numerical generations still need source-coordinate
normalization, not just selected-level agreement.

## Adversarial checklist

1. Literal X⊆Y in ONE normalized Kpt tree; graph reduct agreement is not enough.
2. The old top has an ACTUAL physical seed, not only a topI marker.
3. Compare only c<oldTop; new levels above oldTop are unrestricted.
4. Allowed is a set of SOURCE-coordinate cuts, not numerical target gaps.
5. Microevents such as K4 cuts 10/22 must be represented in Allowed when genuinely planned.
6. No-novelty tests are required only if c is not old-selected and not Allowed.
7. The full physical relation is multi-valued at I2; no false functional B3 identification.
8. Negative L atoms and fake E predecessor bits are not dropped.
9. The crossing pair must come from ONE actual Kpt node.
10. No terminal identity or finite-index bijection is needed for the two tests.
11. The one-sided new→old relation inclusion suffices by the true source monotonicity theorem.
12. The proof never infers old and new outgoing monoid maps are equal.
13. The conclusion is an inclusion/sandwich, not exact identification of all Allowed events.
14. Allowed=∅ recovers selected old-range stability, not full labelled source-record equality.
15. This is not yet a finite-index specialization for actual bare numerical-H+ runs.
16. Henson K-free physical avoidance of new columns remains a separate hypothesis in later applications.
17. No uniform BRD bound, no lower bound, no common source carrier is proved.
18. Compile and audit exact Lean theorem endpoints before claiming kernel validation.
