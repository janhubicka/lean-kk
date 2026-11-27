# Constructed finite selected fronts and retained envelopes — 27 November 2026

## Outcome

This batch constructs the finite selected terminal lists needed by the
actual event-graph application. Kept coding roles are identified with
prescribed original indices, a fresh coded cap is supplied automatically,
and the finite retained levels and complete original pool are constructed.
The selected lists derive the positive-source and nonselected-old-column
conditions of the planned-envelope theorem.

The assembled endpoint is `resolvedFairFiniteSelection_envelope`. It
starts with any finite original selection, including the empty selection,
and arbitrary whole-event auxiliary retention flags. It constructs the
cap, finite prefix, retained levels, pool and selected fronts. Its remaining
seed/pool, selected-age and no-split assumptions are explicit.

This advances the finite projected-diary application obligation. It does
not yet construct legal diary retention flags, prove uniform diary record
bounds, or establish the sharp big Ramsey characterization. The four
remaining major application obligations from the
[preceding event-chronology batch](resolved_event_completion_20261127.md)
remain, with a smaller first obligation.

## Completed local verification

| Gate | Result |
|---|---|
| Normal default `lake build` | **PASS**, exit 0, **4,129 jobs** |
| Normal target importing all six new modules | **PASS**, exit 0, **3,619 jobs** |
| Central Lean audit and strict named-report parser | **PASS**, **1,470 exact reports** |
| Four focused Lean audits and strict parsers | **PASS**, **76 exact reports**, all axiom sets identical to the central audit |
| Axiom-parser self-test | **PASS** |
| Module-coverage parser tests | **PASS**, all three cases |
| Source/import audit and `git diff --check` | **PASS** |

The central script preserves its entire preceding contents as a literal
prefix. All 1,394 inherited names and their axiom sets are unchanged. The
76 additions cover every public theorem in the six new modules. Fourteen
central names are axiom-free; every axiom in the others is `propext`,
`Classical.choice` or `Quot.sound`. No custom axiom or `sorryAx` is accepted.
These are theorem-inventory counts, not a percentage of the remaining
mathematical proof.

The [machine-readable evidence](audits/2026-11-27-finite-selected-front-completion.json)
records all 797 source/audit/configuration hashes, the complete named axiom
inventory, execution outcomes and log hashes. The source is identified
over baseline `be958e2f83b9d962dc641fddc5b2ccca632af051` without a circular
self-hash of the evidence document.

Validation used Lean **4.35.0-rc3** and the same eleven dependency pins as
the preceding batch, including successor tree
`a74c10761303a18649053f2af3a1a1697f032e13`, Ramsey space
`f471b640f11e6b35fbbc3ad74dfa93df5ec3eadc`, and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`. The default import closure reaches
**550 of 728 Kk modules**, plus the root. All six additions are reached;
the unchanged 178 standalone/audit modules remain outside this default
build claim. There are no missing imports or suspicious source tokens.

English proofs were independently reviewed before implementation, and
completed component, cross-module and report reviews passed. This entry
records completed local checks; the consolidated pull request supplies
subsequent hosted and merge evidence.

## Six new modules

| Module in `Kk/` | Public theorems | Contribution |
|---|---:|---|
| `OneGapFiniteCodingFront.lean` | 14 | Constructs an increasing finite enumeration of eligible kept coding names in a given finite pool, with exact range, empty-front handling and size/monotonicity facts. |
| `ResolvedFairCodingSelection.lean` | 11 | Derives the unique original index of each actual coded coordinate and constructs coding retention from a finite original selection. |
| `ResolvedFairRetainedPlan.lean` | 21 | Constructs the finite prefix, paired retained levels, complete retained-role original pool and coding cap; proves exact membership, bounds and endpoint retention. |
| `ResolvedFairSelectedFront.lean` | 8 | Instantiates actual finite fronts, derives positive-source and nonselected-old-zero conditions, and identifies front members with selected originals. |
| `ResolvedFairFiniteSelection.lean` | 14 | Constructs a fresh cap beyond all requested originals, keeps it explicitly, includes every augmented original in the actual finite pool/levels and bounds front size by the requested size plus one. |
| `ResolvedFairSelectedEnvelope.lean` | 8 | Proves cap inclusion at every omitted cut below the cap, derives the actual graph and retained-plan premises, and assembles full planned envelopes with explicit remaining age/no-split and seed inputs. |

The source is additive. Existing Kk theorem files, dependency pins and
manuscript text are unchanged.

## Exact coding-coordinate correspondence

Write a(n) for the padded address of the actual coding position of original
n. Its event is a singleton with the prescribed even raw original name.
If an arbitrary coordinate has a coded role, its own event certificate
therefore identifies its raw vertex with that of one original. Injectivity
of the actual event-vertex enumeration identifies its chronological
position with that original's coding position. The padded coordinate is
then exactly a(n); strict increase of a gives uniqueness.

This proves `resolvedFairEventRole_coded_iff_originalAddress`, rather than
assuming a coding-coordinate image property. Recovering the original
index from an arbitrary coded coordinate uses the explicit
empty-initial-old-pool hypothesis. The actual initial-stage constructor
supplies that condition.

`resolvedFairSelectedKeep` sets coding-event flags using the finite image
of a requested set S under the actual coding-event map. Auxiliary-event
flags remain independent. The resulting exact theorem is

```text
role(v) = coded true  iff  there exists n in S with v = a(n).
```

It handles empty S and supplies the finite original interpretation of the
retained coding roles proved in the preceding batch.

## The selected front is an actual finite list

For a finite partial structure A, complete original pool V and cut c,
the front contains precisely those finite-prefix names v for which

```text
v belongs to V,  c+1 <= A.freeLevel(v),  and role(v) = coded true.
```

The implementation forms this finite set and enumerates it in increasing
order. The exact range theorem includes an empty list. Every entry is
inside the ambient prefix and strictly later than c; the latter follows
from actual free-level eligibility and `freeLevel(v) <= v`.

At an omitted base role, actual geometry classifies every positive later
retained neighbour as kept coding. The exact range theorem therefore puts
that neighbour into the constructed front. An eligible retained name
absent from the front is not kept coding, so the actual graph theorem
gives its entire zero old column. Thus the positive-source and
nonselected-old-zero hypotheses are now conclusions.

For flags constructed from finite S, every front entry is the address of
a unique member of S, and the front size is at most S.card. This is a
terminal-list bound; it is not a bound on the complete diary record.

## Constructed finite levels, complete pool and cap

For a retained coding cap at original index m, let p be its chronological
vertex position, top=a(m), and N=top+1. Form B from the ordinary positions
q<=p whose event flags are true. Define I to contain the anchor zero and
the complete gap/meaningful-coordinate pair for each q in B. Define V to
be every finite-prefix original whose base role is retained.

The resulting levels are finite, bounded by top and contain both zero and
top. At a meaningful coordinate below N, membership in I is equivalent
to retention of its role. Hence an omitted meaningful level has an omitted
base role, supplying the hypothesis needed by the graph argument above.

Dummy originals belong to V even when their own coordinates are omitted
from I. The proof preserves this distinction. Every retained meaningful
original retains its preceding gap, and the actual free-level formula
then retains every pool original's free endpoint. Retained parameter
coverage is also derived from this actual I/V construction.

The cap's free level is top-1. At an arbitrary c<top, the cap need not be
eligible: the immediate preceding dummy coordinate is the boundary case.
But that preceding gap is retained. At an omitted c<top, equality with
top-1 is excluded, so the cap is eligible and occurs in the constructed
front. This applies to every omitted cut below the cap, including omitted
dummy cuts.
No assertion that the coded cap has a zero old column is used.

For an arbitrary requested finite set S, the cap itself is constructed:

```text
m = S.sup(id) + 1,    S+ = insert m S.
```

The cap is outside S, each requested original index is below m, and
S+.card=S.card+1. Coding flags use S+, so the cap is selected by
construction. Every requested address is strictly below top, every
augmented address lies inside the finite prefix and retained pool/levels,
and every front has size at most S.card+1. The extra one explicitly counts
the cap, also when S is empty.

Auxiliary retention is still arbitrary, and the pool is a finite
truncation. The result does not claim that every globally retained
auxiliary event lies below this cap.

## Strongest assembled theorem and its actual remaining assumptions

`resolvedFairFiniteSelection_envelope` supplies S+, its coding flags,
the cap, finite prefix, I, V and every selected front. It derives graph
forbidden avoidance, retained parameter coverage, pair/free-endpoint
retention, positive-source coverage and nonselected-old-column zero.
The previously verified dummy branch supplies full fibres and corrected
B3 at omitted dummy cuts.

The following inputs remain visible in the theorem statement:

- A seed set X bounded by top, an ambient source pool U covering X,
  inclusion U in the constructed V, and retained levels for all seeds.
- At every omitted meaningful cut below the cap, no new split between selected front
  entries with equal complete old ordinary columns.
- At every omitted meaningful cut below the cap, equality of the full canonical
  selected age before and after that coordinate, for every integer graph
  support of the constructed front.

From these data it constructs a full planned Kpt envelope F with

```text
F.map.levelRange = {q | q belongs to I or top < q}.
```

The two ordinary graph premises are no longer caller hypotheses. The
remaining age/no-split statements are not hidden inside a renamed
certificate or assumed envelope. This theorem is an actual conditional
application to the K4 event graph; it is not yet the completed diary
application or a common inverse-source result.

## Remaining application work

1. **Finish the finite projected diary.** Choose the legal auxiliary
   retention flags and seed/pool data for each occurrence, prove the
   meaningful-cut selected-age and no-split conditions, and establish
   uniform complete-record bounds and parser legality. The finite front,
   original correspondence, cap, I/V construction and two graph premises
   proved here are available components of that argument.
2. **Recover a common full labelled inverse source and upper transfer.**
   Equal macrodiaries must determine all retained ordinary tables,
   auxiliary atoms, marked positions and the cap under genuine Kpt maps.
3. **Prove direct history occurrence and the matching lower bound.**
   Unavoidability and the infinite copy-degree conclusions do not follow
   from finite front bounds. The exact targets 24 and 120,487 remain open.
4. **Generalize the actual fair constructor beyond K4.** Generic finite
   enumeration or general forbidden-family interfaces do not supply the
   general-K_ell marker safety and actual construction.

## Review notes and audit inputs

The English arguments and independent review checkpoints are recorded in
[finite selected fronts and assembly](finite_selected_front_english_20261127.md),
[coding selection](resolved_fair_coding_selection_english_20261127.md),
[retained plan](resolved_fair_retained_plan_english_audit_20261127.md), and
[fresh finite cap](resolved_fair_finite_selection_english_20261127.md).

The four focused scripts partition the 76 new names:
`check_axioms_finite_selected_front.lean` (30),
`check_axioms_resolved_fair_coding_selection.lean` (11),
`check_axioms_resolved_fair_retained_plan.lean` (21), and
`check_axioms_resolved_fair_finite_selection.lean` (14).
