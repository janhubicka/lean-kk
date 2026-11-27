# Exact inverse-source recovery at a selected one-gap code (27 November 2026)

## Checked previous checkpoint

The hosted root build at d46964b compiled the integrated NonedgeHistoryCount,
NonedgeBRD24, ResolvedFairCriticalRetention and ResolvedFairRetainedPalette
modules. Only ResolvedFairActualPalette failed: two postponed tactic errors
in K4-family proofs and a rewrite failing to unfold the definitionally equal
padded original address. The patch replaces the family proof tactics by a
direct proof term and supplies a typed reality fact for the if-expression.
The full root and central axiom audit have not yet succeeded at this head.

## English proof of exact inverse-code recovery

Let P be the finite retained ordinary positions of a prescribed envelope,
whose total level range is the anchor, both coordinates of each retained
ordinary position, and all levels strictly above top. Let a(p)=2p+2 be a
selected meaningful address below or equal to top. Suppose F(A) is the
actual G+ prefix at a(p), of size a(p)+1. The source A need not be defined
by an abstract history; it is a genuine preimage under the shape action.

The formula for the image size makes the strictly increasing level map
send the final coordinate of A to a(p). Its image on the whole source
coordinate interval is therefore exactly the set of retained levels
at or below a(p). The tail above top cannot intervene. Since a(p) is a
meaningful coordinate, truncation leaves complete pairs: the anchor and
the two coordinates for every position in R=P intersect [0,p].

There is a canonical increasing enumeration of these paired levels:
start with 0, and at the k-th ordinary retained position r(k), put
2r(k)+1 and 2r(k)+2. Its domain has size 2|R|+1. Since the level map
and this enumeration are strictly increasing and have exactly the same
finite range, their domain sizes agree and all coordinates agree. The
finite enumeration is constructed by sorting R and appending an
increasing tail; only the finite prefix is used.

The successor-tree library already proves that reindexing the entire
image G+ table along the true level map recovers A, not just its positive
relations or old-column age. Substitute the coordinate identity just
proved. The recovered table is literally the one-gap retained code
of the induced ordinary graph on the sorted R. In particular the
auxiliary E table, fake coordinates, directed negative atoms, and
diagonal are all recovered. No comparison of dependent parameter
histories between the two maps is required.

This is instantiated in the actual event graph. For two occurrences,
if their retained ordinary prefix lists have equal length and all
corresponding graph-table entries agree, their source G+ vertices
are equal (by exact finite one-gap graph compression and subtype
extensionality). Apply pointwise for a labelled tuple. This reduces the
sharp orbit step to ordinary finite graph/rank reconstruction.

## Adversarial boundaries

* The level range above top is used only to identify its truncation.
  The statement is not true for arbitrary nonpaired retained plans.
* The last source coordinate maps to the last image coordinate, not
  to the canonical cap height. Source code length is one more than
  its last coordinate.
* Truncating at a gap rather than a meaningful address can leave an
  incomplete pair; the theorem intentionally uses a(p).
* Equal cardinalities or equal local ages alone do not identify the
  actual retained graph. Both directions of its entire finite binary
  table are required.
* The current coarse fixed-terminal retention includes a fresh genuine
  coding cap. It may retain events caused solely by that cap, or extra
  members of a globally large cover block. It is NOT established that
  this record is determined by the legal selected diary. In particular
  the coarse palette is not the verified set of 24 histories.
* The sharp next task is to derive a diary-controlled retention and
  literal retained-table/rank equality from the actual event schedule.
  The older independent-set English proof used a dummy cap, not an
  arbitrary later real terminal. A neutral cap or a proof that the
  cap contributes no extraneous events must be supplied, not assumed.
* The finite history count in #504 is unchanged. The sharp upper
  transfer, lower unavoidability, general K_k and new exact-head
  integrated validation remain open.
