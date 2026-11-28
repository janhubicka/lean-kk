# Event projection batch (28 November 2026)

## Baseline and scope

PR #518 was fully checked and merged. The neutral-cap branch's first
build reported exactly one failed rewrite at resolvedNeutralCapType_level
(Lean run 46150977505). This batch supplies the graph, size and address
explicitly. No new verification claim is made until the combined build
and strict axiom audit pass.

## 1. A genuine restriction of a cover is a cover or equality

Let pi injectively select occupied class labels from a larger class
domain. Lower and upper canonical ages restrict by support images.
Given an intermediate restricted canonical age M, define a full raw
bound B which replaces each image support's upper bound by M's value
and leaves all other upper bounds alone. Image supports have unique
preimages. B lies pointwise between lower and upper, so its canonical
age C is genuine and also intermediate. Its restriction is exactly M:
the upper inequality is the literal raw bound at an image support;
for the lower inequality push a witness saturating M forward into
the full sort domain, assigning zero to unselected sorts. It satisfies
the upper age (by support monotonicity and the previously checked
pushforward theorem), and its mass on an image support is exactly
the corresponding M-support mass by injectivity. Hence it satisfies
B. This proves exact recovery and the full cover excludes a strict
restricted intermediate. If the essential minimal changed support
is not fully occupied, the existing overlap-locality theorem gives
equality; if occupied, its unique preimage has a strict drop.

The restriction MUST use one representative per occupied class.
The terminal-to-class map can be noninjective before the first split.
Duplicating a class can create additional intermediate ages, so applying
the Hasse-cover assertion to that map would be false.

## 2. Exactness and actual event certificates

The round constructor already proved exact old-column labels at the
start of the cover path, but its existential trace discarded the proof.
Keep that fact in the round trace and propagate it along each actual
cover insertion by resolvedClassExact_of_live_extension. Each cover
certificate now stores exactness for its own pre-old pool. This is a
strengthening of proof data, not a new hypothesis on the infinite graph.
The countable fair schedule chooses from the strengthened theorem.

Cover members cannot split any old-equivalent pair, by the actual
column constancy and exactness. A marker's positive terminals belong
to one old class by the certified single-class split result. Thus
only markers can produce a selected split, and a marker cannot split
two different selected classes. For representatives from distinct
occupied classes, actual pre/post age pullbacks give the cover-or-equality
classification just proved.

The complete auxiliary-block age effect is the canonical clipping of
the old canonical age by 3 minus the actual block length on its selected
positive support. This uses the whole witness equivalence for isolated
cliques, not an incorrect raw equality on only one support. If an
event is omitted because its endpoint ages coincide, every intermediate
old pool has exactly the same age by antitonicity. The selected-only
moving front at any code already has both local neutrality properties,
by the checked original coding theorem. No extra cap terminal is needed.
Saturation and a singleton coded class also force its capacity one.

## 3. Two-sort history block reconstruction

For a genuine two-sort profile cover the inclusion-minimal changed
support is unique. Its positive mask and forced clique-block size
are determined by the before and after profile. These are finite
algebraic consequences of the full age poset, not a recomputation of
the 24 accepted histories. A one-class marker in an already split
pair clips the corresponding singleton capacity at two; positivity
of both singleton capacities keeps the joint bound feasible. It is
either equality or one cover. The one-sort marker gives the analogous
unit drop. The existing splitProfile_feasible theorem handles the
true first split (negative child left, positive child right).

## 4. Remaining obligations and adversarial checks

* The actual neutral cap is only a finite witness; it is not an added
  terminal of the infinite copy.
* Cover strictness uses the full essential support; arbitrary overlaps
  or repeated terminal labels are not sufficient.
* Projected age cover classification requires distinct selected old
  columns; before a split, choose one occupied-class representative.
* The marker clipping theorem with nonempty support does not assert
  any spurious constraint for an empty positive support.
* The actual event-level lemmas still need to be assembled along the
  chronological schedule, including projection to occupied classes
  at every endpoint, the true split and coding legality, and literal
  retained graph/rank reconstruction. The singleton coding capacity
  lemma alone is not the mixed-support independent coding formula.
* A separate lower-bound construction must realize every history
  inside every induced copy. The 24 enumeration is already verified.
* Generic restriction works for arbitrary uniform clique bound;
  the actual fair construction in this branch remains K4-specific.

All new proof sources in this batch are candidates. Local Lean is
not available in the current environment; one consolidated exact-head
CI run is required. No manuscript validation markers are promoted.
