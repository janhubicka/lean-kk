# A finite retained plan for the actual event graph

## Inputs and concrete objects

Fix an actual resolved fair event schedule from a bare K4 stage `s0`, an
arbitrary Boolean keep flag on global event occurrences, and a coding
round `n`. Write `p` for its chronological coding vertex position and
`c` for its global coding event index. Assume only, when asserting that
the cap is retained, that `keep c = true`.

Set `top = oneGapAddress p = 2*p+2` and `N = top+1`. Define the finite
set of kept unpadded positions by

`B = {q in range (p+1) | keep (resolvedFairVertexEventIndex s0 q) = true}`.

The retained levels are the actual finite set

`I = oneGapPairedLevels B = {0} union {2*q+1 | q in B} union {2*q+2 | q in B}`.

The ambient original pool is the actual subset of `Fin N`

`V = {v | ResolvedQRetainedBase (resolvedFairEventRole s0 keep v.val)}`.

Thus every dummy original in this finite prefix is in `V`, whether or
not its coordinate belongs to `I`. Meaningful retained originals are
exactly the kept event positions, including retained auxiliary blocks.
The cap is the ambient name `top : Fin N`; it is not removed from the
pool or added through a separate unproved coverage assumption.

These definitions concern an existing event schedule and its roles. They
do not need an empty initial old pool: that hypothesis is needed by other
theorems relating the schedule to exact global graph prefixes, not by
these finite coordinate identities.

## Exact membership and bounds

By the filter definition, `q in B` means exactly `q <= p` and that its
global event is kept. A meaningful one-gap coordinate is uniquely
`2*q+2`, with `q = oneGapIndex v`. In the definition of `I`, such a
coordinate cannot equal the anchor or an odd gap. Its membership is
therefore equivalent to `q in B`.

The existing exact retained-role characterization gives, for every
meaningful coordinate `v`,

`v in I iff v <= top and ResolvedQRetainedBase (role v)`.

For `v : Fin N`, the bound is automatic. Consequently

`v in V iff not oneGapReal v.val or v.val in I`.

The real-coordinate qualification is essential. A dummy has a retained
base role independently of its finite-level membership. Every member of
`I` is at most `top`, since a selected position is at most `p`, and the
anchor and both members of each pair satisfy the bound. Finiteness is
given by the displayed `Finset` construction; the pool is a subset of
the finite ambient type.

## The retained coding cap

The coding event has singleton block `[2*n]`. Its first tagged vertex
position is its event boundary, which is exactly `p`. The positive-block
interval theorem identifies the event containing `p` with the global
coding event `c`. The existing role-at-batch-position theorem and the
coding event kind therefore give

`role (oneGapAddress p) = coded (keep c)`.

Under `keep c = true`, this proves `p in B`, `top in I`, and cap membership
in `V`. The cap's preceding gap also belongs to `I`. This uses actual
coding event and role definitions; no coding-role/finite-selected-list
identification is assumed.

## Endpoints and parameter coverage

If `v in V` is meaningful, the exact membership theorem places `v.val`
in `I`. The existing complete-pair theorem then puts `v.val-1` in `I`.
The actual free-level formula is `v.val-1` at meaningful originals and
zero at dummies. Since the anchor is in `I`, every ambient original in
`V` has its free endpoint in `I`, including dummy originals whose own
coordinate is omitted. Hence no member of the complete pool ends at an
omitted level.

Conversely, if an ambient name has its coordinate in `I`, its role is
retained: use exact membership for meaningful names and the dummy role
otherwise. This yields the `hRet` parameter-coverage premise of
`oneGap_planned_envelope_of_real_selected_neutrality`, in fact without
needing its positive-free-level side condition. A meaningful coordinate
within this prefix is omitted from `I` exactly when its base role is
omitted; this is the precise bridge to the existing actual event geometry.

## Scope

This module constructs the finite paired level set, finite ambient pool
and retained coding cap, and proves their membership, bounds, coverage
and endpoint properties. Keep flags remain arbitrary per global event.
No projected diary, seed set, or seed-level retention is constructed.
The cap is an actual retained coding original; no extra diary cap
admissibility or selected-front interpretation is asserted.

The finite selected coding list and its role correspondence, selected
no-splitting and canonical age equality at omitted meaningful cuts,
legal projected-record parsing and finite record bounds, a common full
inverse source, history and lower-bound arguments, and a general-Kell
fair graph constructor remain separate obligations. Dummy originals in
`V` are deliberately not identified with the finite dummy levels in `I`.

## Review and validation

English proof review: **PASS**, independently completed before Lean
implementation. The review checked the exact meaningful-coordinate
equivalence, the distinction between dummy originals and dummy levels,
actual cap identification, and the absence of an unnecessary empty-pool
hypothesis. Independent review of the completed source also passed. It
checked all twenty-one public endpoints, including actual cap retention,
the complete ambient pool, retained parameter coverage, and the separate
free-endpoint argument.

The parent task's serialized direct Lean check of the final source
**PASSED**, exit code zero, with the pinned Lean 4.35.0-rc3 toolchain. The
diagnostic log at `proof-audit/ResolvedFairRetainedPlan-local.log` is empty.
The only repair after the first check explicitly unfolded the retained
level-set definition in a simplification; no theorem statement changed.

The focused named audit script
`scripts/check_axioms_resolved_fair_retained_plan.lean` checks and prints
the transitive axioms of all twenty-one public endpoints. Its execution,
normal Lake/full-root validation, and the final central named-axiom gate
remain **PENDING**. Compiler calls are serialized by the parent task.

## Final finite-front integration checkpoint — 27 November 2026

This completed checkpoint supersedes pending validation language above.
The normal new-module target passed (3,619 jobs), the default project build
passed (4,129 jobs), all four focused Lean audits and strict parsers passed,
and the central audit accepted all 1,470 exact names, including every one
of the 76 new endpoints. All 1,394 inherited names and axiom sets are
preserved. Only `propext`, `Classical.choice` and `Quot.sound` appear, with
fourteen central names axiom-free. Parser tests, source/import coverage
and diff checks pass. See the [completion report](finite_selected_front_completion_20261127.md)
and [source-hash/axiom evidence](audits/2026-11-27-finite-selected-front-completion.json)
for the precise conditional envelope and remaining application obligations.
