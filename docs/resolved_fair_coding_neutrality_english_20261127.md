# Coding neutrality in the actual chronological graph

## Scope and source

This construction starts from merged main
`ce360818a01188c810d221c2271c9c61f294b235`. It proves the ordinary no-split
and full canonical-age equalities at an actual coding position, before
one-gap padding. The terminal list consists of any finitely many later
original indices; it may repeat indices or be empty.

Write `J(n) = resolvedFairCodingEvent s0 n`,
`p(n) = resolvedFairEventCodePosition s0 n`,
`f = resolvedFairEventVertex s0`, and `E = resolvedFairEventEdge s0`.
The recorded event at `J(n)` is denoted by `e`. The existing schedule
gives `f(p(n)) = 2*n`, while the actual code event has block `[2*n]`.

The new module is `Kk.ResolvedFairCodingNeutrality`. It reuses the generic
induced-image age transport being developed in `Kk.OneGapAgeTransport`.
It does not implement one-gap padding or choose retention flags.

## English proof before Lean implementation

### Use the actual chosen event certificate

The position/location inverse for the round-event enumeration identifies
the location of `J(n)` with the pair consisting of `n` and that round's
last event index. Consequently the existing certificate at `J(n)` is
a `ResolvedEventCertificate (resolvedEvenTail n) (2*n) e`.

Eliminate this certificate together with the proved fact that `e.kind`
is code. The marker and cover constructors are impossible. The code
constructor exposes the actual live state `s` for this exact recorded
event, with

```text
e.preOld = s.old
e.block = [2*n]
e.edge = s.edge
```

It also exposes saturation `s.oldAge = s.futureAge`, exact class labels,
isolation of the coding original, and constancy of its adjacency on
classes. These are the exact witnesses needed below. No new existential
round trace is chosen and silently identified with the recorded event.

First obtain two reusable certificate-level consequences. For any
`ResolvedEventCertificate W r e` of code kind:

1. If `v,w` are in `W` and have equal columns on every member of
   `e.preOld`, exactness identifies their class labels and coding
   constancy gives `e.edge r v = e.edge r w`.
2. If each member of a finite terminal list belongs to `W` and differs
   from `r`, `ResolvedLiveStage.saturatedCode_target_neutral` gives equal
   complete canonical ages on `e.preOld` and `e.postOld`. For the code
   constructor, `e.postOld = insert r e.preOld`. The order of equality is
   chosen as before equals after.

The second consequence concerns the complete canonical support function,
not equality of raw bounds. Neither consequence asserts full Kpt
successor coherence by itself.

### Identify the chronological old pools exactly

Assume `hEmpty : s0.old = empty`, as required by the existing exact-prefix
and injection interfaces. The event-prefix theorem gives

```text
(Finset.range (p(n))).image f = e.preOld.
```

Since the coding block is a singleton and `f(p(n)) = 2*n`, finite-range
successor and image-insertion identities give

```text
(Finset.range (p(n)+1)).image f = e.postOld.
```

These equalities identify the actual chosen code event's pools. They do
not infer an individual-event order by sorting an entire round.

### Transport the old graph and terminal columns

Let `target : Fin d -> Nat` satisfy `n < target i` for every `i`.
The actual terminal names `2*target i` belong to `resolvedEvenTail n`
and differ from `2*n`. Their chronological positions are `p(target i)`.

The existing localized event agreement identifies the final graph with
`e.edge` on `e.postOld` together with this round's live originals.
Therefore it identifies all old-old edges and all old-terminal columns
needed at both finite prefixes. No agreement on unused names outside
that domain is asserted.

The chronological enumeration `f` is injective under `hEmpty`. Apply the
generic induced-image raw-age transport to each prefix, the map `f`, the
chronological graph `E`, and the actual recorded graph `e.edge`. Its
column comparison uses `f(p(target i)) = 2*target i`. The exact image
equalities then identify the two resulting canonical ages with

```text
resolvedTargetAge e.edge 4 e.preOld (fun i => 2*target i)
resolvedTargetAge e.edge 4 e.postOld (fun i => 2*target i).
```

Their equality is the certificate-level coding neutrality proved above.
No injectivity of the terminal list is needed. An empty terminal list
also causes no exception: there are then no nonempty support indices.

For no-split, use the first exact image equality to transfer equality of
all chronological old columns to equality on every member of
`e.preOld`. Apply the certificate-level no-split result to the actual
even terminal names, then transport the new coding bits back by the
same localized agreement.

## Stable main interfaces

The public age endpoint will be named
`resolvedFairEventCoding_targetAge_neutral`, with parameters
`s0`, `hEmpty`, `n`, `target : Fin d -> Nat`, and
`hTarget : forall i, n < target i`. Its conclusion is

```text
resolvedTargetAge E 4 (Finset.range (p(n)))
  (fun i => p(target i)) =
resolvedTargetAge E 4 (Finset.range (p(n)+1))
  (fun i => p(target i)).
```

The public no-split endpoint will be named
`resolvedFairEventCoding_no_split`, with parameters
`s0`, `hEmpty`, `n v w`, `hv : n < v`, `hw : n < w`, and

```text
hOld : forall q, q < p(n) -> E q (p(v)) = E q (p(w)).
```

Its conclusion is `E (p(n)) (p(v)) = E (p(n)) (p(w))`.

Reusable helpers will expose the exact coding-event location and
certificate, both prefix-image equalities, and the two code-certificate
consequences. Before/after age-transport helpers may also be exposed
where useful. Existing modules and their theorem statements remain
unchanged.

## Application boundary

The construction is K4-specific through the existing actual fair-stage
and code-certificate APIs. Its terminal indices must occur strictly
after the coded original. It assumes neither finite selection flags nor
any auxiliary-retention rule. The parent will use it after proving that
all-auxiliary retention leaves only unselected coding events at omitted
meaningful cuts; a separate module transports the conclusions through
one-gap padding. Seed construction, envelope assembly, and bounds on
the number of retained auxiliary events remain separate tasks.

## Validation checkpoint

This English proof was written before the new Lean module. Independent
pre-code review passed. The implementation contains eight public
theorems: two certificate-level consequences, the exact coding location
and its specialized certificate, both exact prefix-image identities, and
the two stable chronological endpoints. Implementation-only graph,
column, and age-transport helpers remain private.

The focused script
`scripts/check_axioms_resolved_fair_coding_neutrality.lean` contains
`#check @` and `#print axioms` for all eight public theorems with their
exact namespaces. Independent completed-source review passed, including
the localized agreement domains and the absence of any substitute event
witness. Serial compiler checks and focused axiom execution are pending.
This agent has not launched Lean or Lake.

## Final all-auxiliary integration checkpoint — 27 November 2026

This completed checkpoint supersedes pending validation language above.
Independent English-first, completed-source, assembly and static integration
reviews passed. The normal new-module target passed (3,624 jobs), the
normal default build passed (4,134 jobs), and the central audit/strict parser
accepted all 1,511 exact names. All 1,470 inherited names and axiom sets are
preserved. The three focused audits cover exactly all 41 new endpoints;
every axiom set agrees with central. Fourteen reports are axiom-free, and
only `propext`, `Classical.choice` and `Quot.sound` appear in the others.
Parser tests, source/import coverage and diff checks pass. See the
[completion report](all_auxiliary_envelope_completion_20261127.md) and
[machine evidence](audits/2026-11-27-all-auxiliary-envelope-completion.json)
for precise scope and the remaining controlled-retention/diary obligations.
