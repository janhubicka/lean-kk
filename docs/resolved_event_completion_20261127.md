# Actual individual events and one-gap geometry — 27 November 2026

## Outcome and verification scope

This batch constructs the **individual marker, cover and coding chronology**
inside the actual countable K4-free construction. It proves exact old pools
before every event and every vertex within an event, whole-block convexity
after one-gap padding, and a concrete canonical G+ source using that order.
It also derives the needed auxiliary nonedges from the actual construction
and supplies the dummy-cut branch of the planned-envelope theorem.

The first of the five application obligations in the
[26 November report](one_gap_local_completion_20261126.md) is now discharged.
The projected-diary obligation has advanced, but the **sharp big Ramsey
characterization remains open** at the four obligations below.

The inventory is **ten new Lean modules and 111 public theorem endpoints**.
The central audit preserves all **1,283 previous names in their original
order**, followed by the new endpoints, for **1,394 distinct names**.
The modules are additive: existing theorem sources, dependency pins and
the manuscript are unchanged.

The complete local integration gate has passed:

| Gate | Result |
|---|---|
| Normal default `lake build` | **PASS**, exit 0, **4,123 jobs** |
| Three normal targets importing all ten new modules | **PASS**, exit 0, **3,614 jobs** |
| Central Lean audit and strict named-report parser | **PASS**, **1,394 exact reports** |
| Five standalone focused Lean audits and strict parsers | **PASS**, **111 reports**, with every axiom set matching the central audit |
| Axiom-parser self-test | **PASS** |
| Module-coverage parser tests | **PASS**, all three cases |
| Source/import coverage and `git diff --check` | **PASS** |

Fourteen central endpoints are axiom-free. Every reported axiom in the
others is `propext`, `Classical.choice` or `Quot.sound`; no custom axiom or
`sorryAx` is accepted. All 1,283 inherited axiom sets also match the previous
verified batch. The complete report-name/axiom inventory, source hashes,
executed commands, log hashes and dependency pins are recorded in the
[machine-readable completion evidence](audits/2026-11-27-resolved-events-completion.json).

Validation used Lean **4.35.0-rc3**, successor tree
`a74c10761303a18649053f2af3a1a1697f032e13`, Ramsey space
`f471b640f11e6b35fbbc3ad74dfa93df5ec3eadc`, and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`. All eleven resolved dependency
pins are unchanged. This records completed local evidence; the consolidated
pull request supplies the subsequent hosted and merge evidence.

## New modules

| Module in `Kk/` | Public theorems | Contribution |
|---|---:|---|
| `ResolvedEventTrace.lean` | 10 | Concrete marker/cover/code certificates and exact successive event pools; positive, distinct and fresh block entries; localized graph transport. |
| `ResolvedRoundEvents.lean` | 6 | Extracts individual events from actual round witnesses, preserving cover-path order and placing the coding singleton last. |
| `ResolvedEventChainOrder.lean` | 7 | Exact finite event pre-pools, flattened vertex sets, no repetitions and pairwise disjoint event blocks. |
| `OneGapEventScheduleOrder.lean` | 3 | Lexicographic order of tagged batch positions, monotone batch location, and exact prefixes inside a batch. |
| `ResolvedFairEventSchedule.lean` | 26 | Actual countable event and vertex enumerations, every intermediate prefix, agreement on every recorded post-old/live domain, increasing coding positions and the prescribed original graph. |
| `OneGapEventRole.lean` | 11 | Roles indexed by global event occurrence, uniform block retention and block convexity with intervening dummy coordinates. |
| `ResolvedEventBirthGeometry.lean` | 10 | Derives old-to-auxiliary nonedges, singleton/clique facts and uniform live bits from concrete birth certificates. |
| `ResolvedFairEventGeometry.lean` | 16 | Transfers that geometry to the actual padded countable graph, including positive-retained-neighbour classification and complete zero old columns for retained non-coding roles. |
| `ResolvedFairEventOneGap.lean` | 8 | Actual canonical G+ sources for the individual-event chronology, with increasing sizes, injectivity and exact ordinary, diagonal and auxiliary atoms. |
| `OneGapDummyCut.lean` | 14 | Zero-row dummy cuts, full fibres, full corrected B3, retained-pool maps, paired endpoint retention and the planned envelope with hypotheses only at omitted real cuts. |

Counts refer to named public theorem declarations, not definitions,
constructors, proof size or a percentage of the final characterization.
Every listed theorem is named explicitly in the central axiom script.

## Actual events, rather than an assumed event schedule

`ResolvedRoundResult.exists_events` starts from the existing finite round
witness. It extracts marker singletons from the actual refinement batch,
keeps the recorded order of the saturated-cover path, and appends the
actual coding singleton. A cover block is nonempty because its recorded
age change is strict; positivity is not an extra schedule assumption.
Sorting is used inside a finite cover block, not to replace the order of
separate events.

An event retains its concrete pre-old pool, finite vertex list, actual
graph table and marker/cover/coding certificate. `ResolvedEventChain`
requires the next old pool to be exactly the union with that block. It
compares the reference graph with each actual event graph only on the
event's post-old pool together with the round's live set. No equality on
unused natural-number names is required. In particular, a coding vertex
may belong both to the event's post-old pool and to that fixed live set.

The finite-chain induction proves that its flattened list contains
exactly the final pool minus the initial pool and has no repetitions.
The pool before an event is the initial pool plus precisely the preceding
event blocks. These facts derive disjointness; it is not assumed for the
extracted list.

Two applications of the positive finite-batch enumeration then enumerate
first the events and then their vertex blocks. For an empty initial old
pool, `resolvedFairEvent_preOld_iff` and
`resolvedFairEventVertex_prefix` identify every actual event pre-pool with
the union of exactly the preceding blocks. The theorem
`resolvedFairEventVertex_prefix_inside` adds exactly the earlier entries
of the current block to obtain every internal vertex prefix.

The actual initial construction supplies the empty-pool condition. It
remains explicit in generic statements where an arbitrary initial stage
could already contain old vertices. The vertex enumeration is injective
and has exactly the fair-limit domain as its range. Event graph agreement
transports to that limit on the required old/live domain.

Each coding event is a singleton and last in its round. Its event index
and vertex position increase strictly with the original index. Thus
`resolvedInitialEventGraph_originals` gives the prescribed original graph
inside the new event-ordered K4-free graph.

## Geometry from actual birth certificates

`ResolvedEventCertificate.auxiliary_old_zero` proves both ordinary bits
between an auxiliary event's entire pre-old pool and its new block are
false. For markers the pre-old pool includes the markers already inserted
from the same refinement batch. For covers it is the actual current old
pool. Coding events are deliberately excluded from this zero conclusion.

The exact-prefix results put every earlier event vertex into a later
event's pre-old pool. Localized graph agreement transfers the zero bits
to the actual limit graph. This proves earlier-code/later-auxiliary
nonedges and nonedges between distinct auxiliary events without an
assumed nonedge premise.

`oneGapEventRole` uses the **global event occurrence index** to identify an
auxiliary block. Equal supports in different events do not identify their
blocks. Retention flags apply uniformly to complete events. Between two
entries of a retained block, every meaningful coordinate belongs to that
same block; the intervening padded coordinates are dummy roles.

The actual graph then satisfies three useful consequences at an omitted
base role:

- A later retained auxiliary has a zero complete old ordinary column.
- A positive later retained neighbour has role `coded true`.
- A later retained role other than `coded true` has a zero complete old
  ordinary column, including the dummy case.

The strongest latter endpoints are
`resolvedFairEvent_positive_retained_is_kept_coded` and
`resolvedFairEvent_later_retained_noncode_old_zero`. Their omission premise
is `not ResolvedQRetainedBase`; dummy roles are retained under this role
predicate. Consequently these are meaningful-role statements and do not
silently handle omitted dummy levels. The separate dummy-cut theorem
below supplies that application branch.

The conclusion `coded true` identifies a kept coding role. It does not
yet identify the vertex with a member of a particular finite selected
terminal list. That identification belongs to the projected-diary proof.

## Dummy cuts and the full planned envelope

At a dummy coordinate the actual one-gap ordinary row and column are
zero. Full next-type fibre agreement and full corrected B3 follow
directly, even when later retained originals have nonzero earlier
columns. The proof therefore does not impose a zero complete old column
on those later originals merely because the current cut is dummy.

Endpoint retention is handled separately from crossing eligibility. For
example, the meaningful original at coordinate four has free level
three, while crossing eligibility at cut three requires free level at
least four. Keeping complete gap/original pairs prevents the endpoint
from being omitted; crossing coverage alone would not do so.

`oneGap_planned_envelope_of_real_selected_neutrality` constructs a full
planned envelope with exact level range

```text
F.map.levelRange = {q | q ∈ I or top < q}.
```

Its selected positive-source, no-split, other-source-old-zero and
canonical-age conditions are required **only at omitted meaningful
coordinates**. The dummy branch is derived from the padding. The retained
pool, seed levels, paired endpoints, finite bound and actual ordinary
conditions at meaningful cuts remain explicit inputs. This generic
envelope theorem applies to arbitrary `ell >= 2`; it does not generalize
the K4-specific fair constructor.

## Concrete canonical G+ source in the new order

`ResolvedFairEventOneGap` applies the existing canonical embedding to the
new event graph and its coding positions. It proves forbidden avoidance,
injectivity, strict size increase and the exact code size
`2 * resolvedFairEventCodePosition s0 i + 3`.

For distinct original indices, the binary atom is the original graph
bit; diagonal atoms are false. The original auxiliary atom is exactly
`decide (i < j)`. In particular,
`resolvedInitialEventOneGapOriginal_binary` specializes to the prescribed
graph `E`, using the actual empty-old initial stage. Thus the concrete
source is synchronized with individual events, rather than only with the
older numerically sorted round schedule.

## Four remaining application obligations

1. **Construct and verify the finite projected diary.** For each selected
   finite occurrence, define its retained event set, complete original
   pool, selected terminal lists and cap. Prove the parser rules and finite
   record bounds. Identify kept coding roles with the finite selected
   terminals, establish paired endpoint retention and pool coverage, and
   prove the full selected-age and no-split conditions at every omitted
   meaningful cut. Then instantiate the new real-cut-only envelope theorem.

2. **Recover one complete labelled inverse source and the upper bound.**
   Prove that equal macrodiaries determine the retained ordinary table
   and marked positions. Combine finite compression with actual G+ code
   recovery to identify the full inverse source, including auxiliary atoms
   and the cap. Establish a common labelled source under genuine Kpt maps
   and apply the countable-source orbit transfer.

3. **Prove direct history occurrence, unavoidability and the lower bound.**
   Realize each legal finite history in every relevant Henson subcopy,
   show distinct records are unavoidable, and combine the lower and upper
   bounds with finite counting. The K4 targets 24 and 120,487 remain
   unproved as exact copy degrees. This batch does not use a JEMS
   characterization as a substitute for that argument.

4. **Extend the actual construction from K4 to general K_ell.** The generic
   envelope and compression interfaces already permit general forbidden
   clique size. The private-marker safety, fair-round construction and
   actual countable graph used in this batch remain K4-specific.

## Proof review and audit inputs

English proofs were reviewed independently before substantial Lean
implementation. Completed source reviews checked event order, fixed-live
overlap at coding, graph-domain restrictions, global block identities,
dummy endpoint arithmetic and the distinction between retained roles and
finite selected lists.

The component notes are
[event extraction](resolved_event_trace_english_20261127.md),
[exact scheduling](resolved_event_schedule_english_20261127.md),
[roles](one_gap_event_role_english_audit_20261127.md),
[birth geometry](resolved_event_birth_geometry_english_audit_20261127.md),
[limit geometry](resolved_fair_event_geometry_english_audit_20261127.md),
[canonical source](resolved_fair_event_one_gap_english_20261127.md), and
[dummy cuts](one_gap_dummy_cut_english_audit_20261127.md).

The five focused audit scripts explicitly partition the 111 new names:
`check_axioms_resolved_individual_events.lean` (24),
`check_axioms_resolved_event_schedule.lean` (36),
`check_axioms_resolved_fair_event_geometry.lean` (27),
`check_axioms_resolved_event_birth_geometry.lean` (10), and
`check_axioms_one_gap_dummy_cut.lean` (14). Their union is checked against
the source declarations and the new central registry entries.

The root imports reach **544 of 722 Kk source modules**, plus the root
itself. All ten new modules are reachable. The unchanged 178 standalone
or audit modules lie outside the default target; the default build does
not certify their separate targets. The source/import scan finds no
missing local imports or suspicious source tokens. The existing strict
axiom-parser self-test and all three module-coverage parser tests pass.
