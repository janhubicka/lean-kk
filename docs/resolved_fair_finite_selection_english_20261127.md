# A finite requested selection with a fresh actual coding cap

## Scope and dependencies

This follow-on construction combines `ResolvedFairCodingSelection`,
`ResolvedFairRetainedPlan`, and `ResolvedFairSelectedFront` in the current
batch based on main `be958e2f83b9d962dc641fddc5b2ccca632af051`.
It supplies an actual finite retained plan containing every requested
original, with a fresh coding cap counted in the selection. The cap is
chosen explicitly; no eventual bound or extension is assumed.

Write `a(n) = resolvedFairOriginalAddress s0 n` and
`J(n) = resolvedFairCodingEvent s0 n`. The original-address map is already
proved strictly increasing, and the flag at `J(n)` is already known
exactly for any finite original selection.

## English proof before Lean implementation

### Choose and count the cap

For a finite set `S : Finset Nat`, put

```text
m = resolvedFairSelectionCap S = S.sup id + 1
Splus = resolvedFairSelectionWithCap S = insert m S
```

If `n` belongs to `S`, the finite supremum property gives
`n <= S.sup id`, hence `n < m`. Applying this to `m` itself would contradict
irreflexivity, so `m` does not belong to `S`. The finite insertion formula
therefore gives `Splus.card = S.card + 1`.

Every `n` in `Splus` is either `m`, or belongs to `S`. Thus every such
index satisfies `n <= m`. These arguments also apply when `S` is empty:
its natural supremum is zero, the chosen cap is one, and `Splus` is the
singleton containing one. The construction does not claim that this is
the smallest possible cap.

### Keep exactly the augmented coding selection

Define

```text
resolvedFairFiniteKeep s0 S auxKeep =
  resolvedFairSelectedKeep s0 Splus auxKeep.
```

The existing coding-flag theorem gives, for every `n`,
`resolvedFairFiniteKeep s0 S auxKeep (J(n)) = decide (n in Splus)`.
In particular the flag at the actual cap event `J(m)` is true. At every
original address `a(n)` with `n in Splus`, the existing address-role
formula gives role `coded true`. This is a retained base role.

The auxiliary flags remain arbitrary on whole event occurrences, exactly
as in `resolvedFairSelectedKeep`. Nothing in this construction claims
that every globally retained auxiliary event lies below this finite cap.

### Fit all requested originals into the actual finite retained plan

Use the existing retained-plan parameters with cap index `m` and the
constructed keep flag:

```text
top = resolvedFairRetainedTop s0 m = a(m)
N = resolvedFairRetainedSize s0 m = top + 1
I = resolvedFairRetainedLevels s0 (resolvedFairFiniteKeep s0 S auxKeep) m
V = resolvedFairRetainedPool s0 (resolvedFairFiniteKeep s0 S auxKeep) m.
```

For `n in S`, strict increase of `a` and `n < m` give `a(n) < top`.
For every `n in Splus`, monotonicity and `n <= m` give `a(n) <= top`,
hence `a(n) < N`. This yields a typed ambient vertex
`resolvedFairFiniteSelectionVertex s0 S n hn : Fin N` with value `a(n)`.

Each `a(n)` is a meaningful one-gap address. Its role is `coded true`,
and its coordinate is at most `top`. The existing
`resolvedFairRetainedLevels_of_retained_real` theorem therefore puts it
in `I`. The definition of the retained pool, or the existing
`resolvedFairRetainedPool_of_level` theorem, puts its typed ambient vertex
in `V` as well. In particular these statements include the fresh cap
itself, while the strict bound below top is reserved for the originally
requested members of `S`.

No empty-initial-pool assumption is needed for these forward address,
flag, containment, and retention assertions. They use only the actual
coding-position and address-role APIs.

### Bound every selected front and count the cap

For any finite prefix size `N`, any pool `V : Set (Fin N)`, and any cut,
apply `resolvedFairSelectedFrontSize_le_card` with `Splus`. The result is

```text
resolvedFairSelectedFrontSize s0
  (resolvedFairFiniteKeep s0 S auxKeep) N V cut <= S.card + 1.
```

This theorem retains `hEmpty : s0.old = empty`, exactly as the existing
front-cardinality theorem does. Its proof uses the previously derived
inverse correspondence from coded roles to actual original indices.
For the actual initial stage, `hEmpty` is supplied by `rfl`.

The fresh cap is part of `Splus` and is counted by the extra one. Its
ordinary old column is not assumed zero. Eligibility of the cap in a
particular cut's selected front is a separate statement proved by the
parent's integration module from the retained preceding gap and omitted
cut condition; this module does not claim eligibility at every cut.

## Planned public interface

New module: `Kk.ResolvedFairFiniteSelection`.

Definitions:

- `resolvedFairSelectionCap`;
- `resolvedFairSelectionWithCap`;
- `resolvedFairFiniteKeep`;
- `resolvedFairFiniteSelectionVertex`, taking a proof that its original
  index belongs to `resolvedFairSelectionWithCap S`.

Theorem names:

- `resolvedFairSelection_lt_cap`;
- `resolvedFairSelectionCap_not_mem`;
- `resolvedFairSelectionWithCap_card`;
- `resolvedFairSelectionWithCap_le_cap`;
- `resolvedFairFiniteKeep_code`;
- `resolvedFairFiniteKeep_cap`;
- `resolvedFairFiniteSelection_role`;
- `resolvedFairFiniteSelection_address_lt_top`;
- `resolvedFairFiniteSelection_address_le_top`;
- `resolvedFairFiniteSelection_address_lt_size`;
- `resolvedFairFiniteSelectionVertex_val`;
- `resolvedFairFiniteSelection_mem_levels`;
- `resolvedFairFiniteSelection_mem_pool`;
- `resolvedFairFiniteSelectedFrontSize_le_card`.

## Remaining scope

The construction remains K4-specific through the existing fair-stage
constructor. It supplies finite selection, containment, retention, and
the front-size bound. It does not add a no-split proof, selected-age
neutrality, a projected diary, a parser, or an upper big Ramsey theorem.
The parent owns cap-front eligibility and full envelope assembly.

## Validation checkpoint

This English construction was written before the new Lean module.
Independent pre-code review passed, including the separation between
forward retention and the inverse correspondence used by the front-size
bound. The module now implements the four definitions and fourteen
theorems listed above. Independent completed-source review also passed.
The focused script
`scripts/check_axioms_resolved_fair_finite_selection.lean` contains
`#check @` and `#print axioms` for each of the fourteen public theorems.
Serial central compiler and axiom checks are pending. No Lean or Lake
process has been launched by this agent for this follow-on module.

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
