# Countable chronological batches (26 November 2026)

## Purpose and exact scope

The one-gap partial structure already embeds any given countable ordinary
graph. The missing enumeration issue is different: names allocated while
building a resolved graph need to be read in chronological event order.
`OneGapCountableSchedule.lean` supplies this enumeration for a sequence of
finite, nonempty batches. It proves the enumeration and its finite-prefix
and convexity properties; it does not assume an enumeration with those
properties.

The tagged schedule works without any assumptions about vertex names.
For actual lists of vertices, no repetition within a batch and disjointness
between batches imply injectivity of the resulting vertex enumeration.
Its range is exactly the union of the batches.

## English proof before Lean

Let batch n have positive length s(n). Put b(0)=0 and
b(n+1)=b(n)+s(n). The sequence b is strictly increasing, and b(n)>=n.
For each natural k, there is therefore a least n with k<b(n+1).
Minimality gives b(n)<=k, so k-b(n) is a valid index in batch n.

The map taking tagged entry (n,j) to b(n)+j is inverse to this location
map. Indeed its value lies in the half-open interval [b(n),b(n+1)),
and these intervals are disjoint. This proves a genuine bijection from
the tagged entries to the natural numbers.

Each batch occupies exactly one half-open interval. Hence every index
between two indices of the same batch remains in that batch. Positions
below b(n) are exactly entries from batches with index below n. This
is the precise whole-block convexity and prefix property needed for
chronological reindexing.

Read the actual vertex list at the located index. Its range is the union
of the lists because the tagged position of each list entry maps back to
it. If two resulting vertices agree, disjointness first forces equality
of the batch indices; no repetition within the common list then forces
equality of the entry indices. The tagged bijection gives equality of
the chronological indices.

## Adversarial boundaries

* This module's interface requires each batch to be nonempty; its proof
  obtains unbounded cumulative lengths from b(n)>=n. A more general
  enumeration can allow empty batches and assume only unbounded
  cumulative lengths. To use the present interface, empty stages can
  be omitted or grouped with a coding event; they must not silently
  be treated as positive blocks.
* A union of finite old pools alone does not determine the order of
  events inside a round. The application must supply the actual ordered
  marker/cover/code batches.
* `ResolvedFairLimit` on PR #512 supplies an infinite K4-free graph and
  finite round traces. Extracting a coherent batch sequence with the
  required block labels from those traces remains a separate application
  theorem. This module does not assert that extraction.
* Batch convexity concerns the chronological enumeration, not the old
  numerical names. No monotonicity of the allocation of old names is
  required.
* No new Ramsey bound, macrodiary characterization, or infinite resolved
  diary is asserted by these scheduling lemmas.

The parent review checked the least-boundary argument before the Lean
implementation and requested the unconditional tagged bijection to keep
the construction independent of vertex-name disjointness.

## Local validation

The complete 265-line module, containing 19 theorem declarations, passed
`lake env lean Kk/OneGapCountableSchedule.lean` with Lean 4.35.0-rc3.
Thirteen focused transitive-axiom reports passed: one uses no axioms;
the others use only `propext`, `Classical.choice`, and/or `Quot.sound`.
No `sorry`, `admit`, or custom axiom occurs in the module. This is the
local module check, not a claim about the full project's build.

Focused endpoints: `oneGapBatchBoundary_strictMono`,
`oneGapBatchIndex_bounds`, `oneGapBatchIndex_eq_iff`,
`oneGapBatchPosition_injective`, `oneGapBatchLocation_position`,
`oneGapBatchPosition_location`, `oneGapBatchLocation_batch_iff`,
`oneGapBatchLocation_convex`, `oneGapBatchLocation_before_boundary`,
`oneGapChronologicalVertex_at_position`,
`oneGapChronologicalVertex_range`, `oneGapChronologicalVertex_prefix`,
and `oneGapChronologicalVertex_injective`.
