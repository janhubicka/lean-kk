# Independent mathematical review of the selected-TOP B3 proposal

24 November 2026. Reviewer: generation-zero task, independent of the author.

Reviewed `docs/selected_top_age_neutral_b3_english_20261124.md`, SHA-256
`2c35cb5439a6680618a809d332e26228352a72c7d7f19b4c296c90e0a9098e80`.

The proposed K4, height-k>=3 implication is mathematically sound. This is
approval of the precise English argument, before claiming compilation or
an instantiated infinite resolved-Q construction.

## Numerical sandwich

Every complete numerical block for a Q base q<b is strictly below p(b,g),
including when g=0. For a later selected TOP, all of that block's ordinary
bits are exactly the Q bit, including its TOP-to-TOP bit. A finite clique
in the Q common-neighbour pool lifts in base order to increasing physical
generations. K4-freeness bounds the relevant cliques by three, so height
k>=3 suffices for this argument.

Conversely, every positive common numerical neighbour of a nonempty support
is a real coordinate. Its bounded-generation address and position at most
p(b,g) force its base at most b. A numerical clique cannot contain two
copies of one base, because those copies are nonadjacent. Projection is
therefore injective and preserves both directed Q edges and the common
TOP column. These facts give the claimed capacity inequalities.

At positive g there may be partial copies of the current base in the old
physical prefix. The proof correctly uses inequalities around the complete
old and new Q prefixes; it does not assert an unsupported equality between
all physical raw bounds and an endpoint Q raw bound. Subtraction from 3
reverses the capacity inequalities, and canonicalizer monotonicity then
gives the displayed canonical-age sandwich. Equality at the two Q endpoints
forces equality of the two physical canonical ages. No pointwise identity
of arbitrary raw and canonical capacities is used.

## Corrected-B3 transfer

The proposed contradiction keeps the complete initial ordinary socle and
both directions of every old/future column, including negative bits. Thus
the extracted ordinary continuation can be given genuine selected-TOP
labels before applying `finiteOldFuture_free_iff_canonical_support`.
The future graph is arbitrary and its labels may repeat; the reference-age
theorem quantifies over all its cliques, so repetitions introduce no gap.
Deleting and restoring the cut changes only the old prefix in this
comparison. Applying the exact finite-age characterization in both
directions yields the asserted contradiction.

The chosen-output coverage premise is sufficient even if several marked
originals have the same old type with different proposed next types: every
actually chosen output still has a physical representative. The marked-only
B3 argument does not need no-I2 to enforce a different uniqueness property.
The existing transfer to the full closure retains its no-I2 and represented
source hypotheses. The empty-source case is correctly isolated. No E
structure is assigned to the arbitrary ordinary continuation.

## Scope and necessary distinction

The proposal is specifically about the K4 reference age, whose raw bound
is 3 minus old common-neighbour clique capacity. It must not be advertised
as an arbitrary-forbidden-family result. The generation-zero structural
argument needs only singleton neutrality plus selected no-split, but B3
needs equality of the full canonical age on every nonempty support.

The example with old columns (1,0),(0,1) and a new (1,1) column is a valid
separation: singleton values stay (2,2), while the mixed capacity drops
from 3 to 2. An arbitrary future triangle of labels (x,x,y) is permitted
before the cut and forms a K4 with the restored base. The old selected
profiles are distinct, so no-split can hold. This is a real failure of the
weaker singleton-only B3 claim, not a failure of the proposed theorem.

For a whole omitted block, endpoint age equality transfers to every
intermediate original only with fixed future-terminal labels, or the
stated pullback from changing class labels. With that requirement,
monotonicity under old-prefix extension justifies the interpolation,
including inserted dummies. The construction still has to realize those
actual finite-prefix ages and the descending Plan inclusion. The proof
does not discharge those remaining application obligations.

## Independent source review of the numerical-prefix age module

The new `Kk/NumericTopNeutralPrefixAge.lean` was read against
`FullRealGenerationCapacity.lean` and the reviewed English argument.
The complete-real lower pool, prefix inclusion, and upper common-pool
inclusion are correct. A nonempty support supplies a positive actual
TOP bit and hence a bounded real address; bounded block order places its
base at most b. The exact TOP column then supplies every support bit.
The arbitrary-ell and arbitrary-k intermediate result is legitimate:
the existing complete-real capacity equality lifts old cliques using
all TOP copies, whose TOP-to-TOP gate is open, and therefore does not
need a K4 clique-size bound. Empty sort/support cases are vacuous at the
support interface, and repeated sort labels are harmless.

The raw inequalities reverse the capacity bounds correctly, monotone
canonicalization preserves their directions, and endpoint neutrality
composes to the claimed equality in both directions. Total numerical
ordinary L does not require N carrier bounds for this calculation;
physical source applications still require genuine Fin N names. No
semantic defect was found. This paragraph reports source review only,
not compilation or a completed B3 application.
