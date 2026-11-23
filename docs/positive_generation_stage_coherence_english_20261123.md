# Positive lower generations: an old coordinate determines the full stage cut bit

## Status and scope

This statement and English proof precede implementation. Independent review and
kernel validation are pending. It continues the actual resolved-Q upper argument
on the published source baseline. It does not rely on the unavailable earlier
20-module continuation, except that the complete equal-cut reconstruction lemma
is to be restored and checked separately before the final composition.

The result concerns every eligible original in the complete current stage pool,
not merely originals in a marked selected terminal tuple. It assumes the real
higher-stage inclusion in a proposed Plan and the existing chronological role
axioms. It does not assume age neutrality, auxiliary-block convexity, selected
no-split, a final no-fork predicate, or a no-I1/no-I2 conclusion.

## Common data and hypotheses

Let `E : Nat -> Nat -> Bool`, `k N : Nat`, `U : Finset (Fin N)`, and
`J Plan : Set Nat`. Put

```
K := normalizedGraphModel E
A := finiteNumericH K k N
Stage := hStageOriginals K k N U J
name := hOriginalName Stage
```

Use the following bounded-generation repair of the existing resolved-Q interface:

1. `hJPlan : J ⊆ Plan`.
2. A role function `role : Nat -> ResolvedQBaseRole` and
   `hQ : ResolvedQChronologicalAxioms role E`.
3. Every bounded real address in the actual root cap has dummy base role:
   `∀ v : Fin N, v ∈ U -> ∀ j m, m ≤ k -> v.val = hPosition k j m -> role j = .dummy`.
4. Every actual positive-free-level Plan original is either a selected TOP
   coding original or an original from a retained auxiliary block:

```lean
hPlanShape : ∀ v : Fin N, v.val ∈ Plan →
  0 < (finiteNumericH (normalizedGraphModel E) k N).freeLevel v.val →
  ∀ j m : Nat, m ≤ k → v.val = hPosition k j m →
    (role j = .coded true ∧ m = k) ∨
    (∃ block : Nat, role j = .auxiliary block true)
```

These retain the mathematical content intended by
`resolvedQ_stage_omitted_positive_name_is_selected_top` in
`Kk/TrackDPlannedStageRoles.lean`, but add the necessary `m ≤ k` guards to
the root and Plan contracts. In an AlgorithmRun application, take the literal
current-stage set `J = Run.I (cut+1)`. No assertion about `Run.I 0` or its final
original pool is used.

### Why the generation guard is necessary

The existing interfaces quantify over unbounded `m : Nat`. The actual definition
in `SuccessorTree/V10/BlockOrder.lean` is

```
hPosition k j m = 2 * (k+1) * j + 2*m.
```

Therefore an address has noncanonical aliases when m is unbounded. For example,
`hPosition 2 2 2 = 16 = hPosition 2 1 5`. A genuine TOP dummy cap at base 2
with an earlier meaningful coded base 1 satisfies the intended root condition,
but the existing unbounded condition would force base 1 to be dummy as well.
Similarly `hPosition 2 1 2 = 10 = hPosition 2 0 5`; a selected TOP at base 1
would make the unbounded Plan condition impose a retained role on base 0,
even if base 0 is the initial isolated dummy. This is a hypothesis-formulation
obstruction, not a failure of the numerical-H construction.

The guards restrict assertions to the canonical generations `0,...,k`, where
`hPosition_injective_bounded` gives unique decoding. They weaken the old
contracts to their intended content and do not alter any proved old theorem.
The old theorems remain valid under their stronger displayed assumptions.

### Bounded stage-role and positive-name helpers

A first helper must establish the same stage-name classification from the
bounded contracts, for an actual address with an explicit `m ≤ k`. Its proof
uses membership of `name v` in `Stage`: either it is in U, where the bounded
root contract applies, or its address is in J with positive free level, where
`J ⊆ Plan` and the bounded Plan contract apply.

A second helper applies the already checked ordinary-base theorem
`resolvedQ_omitted_base_positive_retained_is_selected_coding`. Together with
that stage-name classification and `E b j = true`, it eliminates dummy and
auxiliary possibilities and gives `role j = .coded true` and `m = k`.
This helper retains explicit `b < j`, `m ≤ k`, omitted base role, actual stage
membership/address, and the actual positive base edge. It introduces no
age or full-source conclusion. The positive-neighbour decoder supplies precisely
this generation bound in both directions of the first endpoint below.

## First endpoint: exact ordinary column equality on the entire stage

For `b g : Nat`, assume

- `hg : g < k`;
- `hCut : hPosition k b g < N`;
- `hOmitted : ResolvedQOmittedBase (role b)`.

Write `c := hPosition k b g` and `q := hPosition k b 0`. For every
`v : Fin Stage.card` satisfying genuine eligibility

```
hFree : c + 1 ≤ A.freeLevel (name v).val,
```

prove the exact Boolean equality

```lean
A.L.binary c (name v).val (0 : Fin 1) =
  A.L.binary q (name v).val (0 : Fin 1)
```

The first endpoint deliberately allows `g = 0`, where it is tautological.
The strict hypothesis `0 < g` is needed only when using q as an already old
coordinate in the second endpoint. The column assertion is about ordinary L;
complete L+/E next-type equality is the separate composition below.

### English proof

The literal address formula gives `q ≤ c`. Thus `q < N`, and `hFree` implies
`q+1 ≤ A.freeLevel (name v).val`. Also `0 < k` follows from `g < k`.
It suffices to compare positivity of the two Boolean bits in both directions.

Suppose the c-bit is true. The already proved
`finiteNumericH_eligible_lower_cut_neighbour_is_higher` gives a genuine later
base `j > b`, a generation `m` with `g < m ≤ k`, the exact address
`(name v).val = hPosition k j m`, and `E b j = true`. This uses genuine free
level eligibility, not the unjustified implication from a larger numeric
address alone.

Apply the bounded positive-name helper proved above to this very
stage name and this actual base edge. Its conclusion is
`role j = .coded true` and `m = k`. The numerical-H gate from the old generation
zero copy of b to the later TOP copy of j is open because `0 < k`.
`hNumericBinary_real_forward_iff` therefore gives the q-bit true.

Conversely, suppose the q-bit is true. Apply the same physical positive-neighbour
theorem at generation zero, using the derived eligibility at q. It yields
`b < j`, `0 < m ≤ k`, the exact same kind of actual stage address, and
`E b j = true`. The same bounded whole-stage role theorem forces `m = k`. Since
`g < k`, the numerical-H gate at c is now open, giving the c-bit true.

Thus the two bits are simultaneously true, and Boolean case analysis yields
literal equality, including their negative values. This bidirectional argument
also covers auxiliary E addresses or other stage names which have no positive
ordinary cut bit: it never assumes that every stage name has a real address.
It derives a real address only from an actual positive bit.

## Second endpoint: complete next-type coherence on every eligible stage name

Retain all common hypotheses and require additionally `0 < g`. Let
`v w : Fin Stage.card` satisfy eligibility at c, and suppose

```lean
A.partialTypeAt c (name v).val = A.partialTypeAt c (name w).val.
```

Then prove

```lean
A.partialTypeAt (c+1) (name v).val =
  A.partialTypeAt (c+1) (name w).val.
```

### English proof

Since `0 < g`, the literal address formula gives `q < c`. Evaluate the equality
of complete old types at the forward ordinary atom from the old socle
coordinate `q` to the distinguished type vertex. Concretely, apply
`PartialTypeWithE.lReduct`, identify the reducts using
`partialTypeAt_lReduct_eq_ofAgeModel`, and evaluate binary at
`(some ⟨q, q<c⟩, none, 0)`. This gives

```
A.L.binary q (name v).val 0 = A.L.binary q (name w).val 0.
```

The first endpoint applied to v and w transports that equality to c. The base
symmetry `hQ.sym` implies symmetry of actual numerical-H ordinary L by
`hNumericBinary_symmetric_of_base`. Apply
`full_equal_ordinary_cut_column_determines_next_type` to A, the actual originals
`name v` and `name w`, their two eligibility facts, the derived equality of c-bits,
and their complete old-type equality. This gives the required complete next-type
equality, including all negative L bits and both auxiliary E directions.

## Source interfaces and proof boundaries

- `Kk/TrackDPlannedStageRoles.lean`:
  `ResolvedQChronologicalAxioms`, `resolvedQ_stage_name_shape_of_planned_levels`,
  and the ordinary-base classification used to build the bounded repair.
  The unbounded generation contracts are not imported as application hypotheses.
- `Kk/PhysicalLowerRealCutNeighbour.lean`:
  `finiteNumericH_eligible_lower_cut_neighbour_is_higher`.
- The numerical constructor's `hNumericBinary_real_forward_iff`,
  `hNumericBinary_symmetric_of_base`, and literal `hPosition` formula.
- `partialTypeAt_lReduct_eq_ofAgeModel`; the exact old-bit extraction pattern is
  already used in `Kk/K4GenerationZeroSourceSeparator.lean`.
- The separately restored `Kk/EqualCutFullType.lean` supplies complete equal-cut
  reconstruction.

This closes a concrete whole-stage coherence step at positive lower generations.
It does not yet lift the result through all closure representations to no-I1
and no-I2, prove the higher-stage inclusion itself, prove full corrected B3,
construct the actual role/Plan assignment, or establish a common labelled orbit.
The first-generation case `g = 0` remains a separate geometric problem: q equals
c there and is not part of the old prefix. Dummy isolation and the corrected
block-convexity-modulo-dummies argument are relevant to that separate case.

## Adversarial checks to perform before implementation

1. The forward and reverse implications both use actual stage names; no chosen
   future selected tuple substitutes for Stage.
2. Eligibility at q is derived from eligibility at c, rather than assumed.
3. Positive-neighbour decoding supplies `b < j`, eliminating the reverse
   numerical generator orientation.
4. The role theorem forces generation k even when the positive bit originated
   at q, where its first decoding only provides `0 < m`.
5. The proof covers false cut bits and addresses with no ordinary L edges.
6. The top-top special gate is irrelevant because the tested generation has
   `g < k`; the endpoint must not be used at `g = k`.
7. Strict oldness q<c is used only for the complete coherence endpoint and
   requires `0 < g`.
8. The complete old-type equality includes auxiliary E and all negative bits;
   equality of canonical ages cannot replace it.
9. No block interval or singleton-neutrality premise is silently introduced.
10. Both root and Plan contracts quantify only bounded generations; otherwise
    the noncanonical address aliases can make the application hypotheses false.
11. Whole closure no-I1/no-I2 and descending Plan inclusion remain downstream
    obligations; this endpoint must not be described as full boringness.
