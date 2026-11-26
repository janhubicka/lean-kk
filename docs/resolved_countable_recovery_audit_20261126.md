# Recovering the actual countable K4 construction

## Provenance and integration boundary

Recovered from PR #512, immutable source
`4ba24e5bff3686b4ff102c9aa9f1920fca8a6d3d`, on
`validation/upper-continuation-20261123`:

* `ResolvedLiveFutureAge`
* `ResolvedLiveCoverNormalization`
* `ResolvedLiveCoding`
* `ResolvedLiveSelectedProjection`
* `ResolvedLiveRefinement`
* `ResolvedLiveRound`
* `ResolvedFairLimit`

The original reachable `Kk.ResolvedFairLimit` source closure contains
126 Kk modules. At extraction baseline
`47307be2d4b4e3ac365409a9c063094f51823f79`, exactly these seven were
absent; the other 119 were byte-identical between that baseline and
the immutable PR #512 source. No other PR #512 changes were needed
to recover this construction. Subsequent integration removed unused
imports in `LaterSelectedMixedPools` and `HensonI3PatternSize`, without
changing their proofs or dependency pins; that optimization has its
own local build and integration evidence. The byte-identity count
refers to the extraction snapshot.

The original English-first notes are retained unchanged:
`resolved_live_future_normalization_english_20261126.md` and
`resolved_fair_rounds_english_20261126.md`. Their historical statements
about then-pending validation are not evidence that the recovered
source has passed a new build.

## Independent mathematical review before recovery

The future age is defined from actual finite cliques in the whole live
set, through their finite normalized multiplicity vectors. An attained
maximum is proved for each support. It is not assumed that the future
realizes every permitted continuation.

Fresh marker and clique blocks change only fresh names. The complete
old/live graph is preserved, in both edge directions. Auxiliary blocks
are anticomplete to the earlier old pool. Their relative K4 safety
is checked on arbitrary finite subsets of the whole live set.

The two marker refinements first isolate the vertex being coded and
then make its adjacency constant on every active class. Saturation
preserves that complete-column partition. Thus coding deletes a
singleton class; an actual maximizing clique on surviving labels
avoids the coded vertex. That is why the proof of canonical reference
age neutrality is valid. Merely deleting one vertex from a nonsingleton
class would not suffice.

The infinite construction uses even names for the prescribed graph
and fresh odd names for auxiliary vertices. Every old or live vertex
remains old or live at the next stage, and every edge between such
vertices is preserved. Every even name is eventually old. The limit
edge is read from any witnessing common old stage and is independent
of that choice. Unused names are isolated. A finite clique is contained
in a single actual stage, so the limit remains K4-free.

Two harmless differences from the historical prose are made explicit:
the initial temporary table can have arbitrary edges on unused odd
names (its safety invariant concerns the actual old/live domain), and
the limit chooses an arbitrary witnessing stage rather than the least
stage. Preservation makes the latter choice immaterial; the final
definition explicitly isolates names outside the actual union.

## Concrete source repair

The historical failing proof was the private `capacity_congr_on` in
`ResolvedLiveCoverNormalization`: rewriting an equality between
filtered powersets did not match the concrete capacity expression.
Replace it by the existing induced-image capacity theorem with the
identity map and the given edge equality. This proves the same
statement without changing any hypotheses or definitions. Its one
additional import is `Kk.FiniteCliqueEmbeddingTransport`.

The first local pass then reached two previously uncompiled details in
`ResolvedLiveRefinement`: the column-profile calculation needed its
final definitional reduction, and destructuring the mixed-class
certificate removed a name used later. Add `rfl` after the profile
rewrite and preserve the certificate before destructuring it. These
repairs change no mathematical statements or hypotheses.

In `ResolvedLiveRound`, the final neutrality comparison is explicitly
folded back to `resolvedTargetAge` before applying its earlier capacity
calculation, and the four bare-stage transfers explicitly unfold
`ResolvedLiveStage.toBare`. These are definitional reductions of the
same expressions; the round construction and its premises are unchanged.

In `ResolvedFairLimit`, the even-name injectivity calculation explicitly
reduces its division-map application before arithmetic, and the
live-domain successor proof selects the right disjunct before rewriting
the live-set index. This avoids a rewrite through the dependently typed
stage in the other disjunct. Both are elaboration repairs of the original
proof, with no change to its statements.

## Exact endpoint scope

`resolvedFair_exists_graph` takes an arbitrary symmetric, loop-free
graph E on the naturals with every finite clique of size below 4.
It constructs an actual coherent infinite graph Q, proves symmetry,
loop-freeness and K4-freeness of Q, proves
`Q (2*i) (2*j) = E i j`, and supplies an actual finite resolved-round
trace for every coded even original.

The subsequent endpoints transfer complete old/live columns to Q,
and prove actual coding reference-age neutrality and no new split
on surviving original terminals. Target labels may repeat or be empty.

This is stronger than a conditional statement assuming an existing
resolved graph. It is still not the complete one-gap diary theorem:
chronological extraction of individual event batches, their projected
record parser, the full ordinary-to-Kpt application, occurrence-independent
inverse-source codes, arbitrary-history occurrence, and final big Ramsey
bounds remain separate. The fair construction here is K4-specific;
it does not construct the general K_ell-free resolution.

## Validation

All seven recovered modules passed normal, serialized local Lake
builds with the pinned Lean 4.35.0-rc3 toolchain after the repairs
listed above. Individual build logs are under
`proof-audit/serial-build/`.

The final normal default `lake build` also passed, completing 4,113
jobs. The central named transitive-axiom gate accepted exactly 1,283
reports: 14 were axiom-free, and the other reports used only
`propext`, `Classical.choice`, and `Quot.sound`. These completed checks
and their evidence are recorded in
[the local integration report](one_gap_local_completion_20261126.md)
and [the machine-readable audit](audits/2026-11-26-local-one-gap-completion.json).

The final verified Ramsey dependency pin is
`f471b640f11e6b35fbbc3ad74dfa93df5ec3eadc`; the successor-tree dependency
remains at `a74c10761303a18649053f2af3a1a1697f032e13`. This is the final
integrated dependency state. The earlier 119-module byte-identity
comparison applies specifically to extraction baseline
`47307be2d4b4e3ac365409a9c063094f51823f79`, before the later import-only
cleanup, rather than to every file in the final checkout.

The earlier PR #512 failure is preserved as provenance, not treated
as successful validation of the repaired source. The two recovered
historical English notes remain unchanged.
