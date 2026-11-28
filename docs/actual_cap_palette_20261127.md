# Actual cap/prefix pairs and uniform palette coverage (2026-11-27)

## English proof (prepared before the Lean implementation)

Fix a finite set S of requested original indices, and n = max(S)+1
(the implemented cap is sup(S)+1, including S empty). The finite
ambient prefix has N = a(n)+1 coordinates, where a(i) is the actual
padded original address, twice the chronological code position plus
two. Its full original cap U is one of the initial seed types. Its
free level is a(n)-1, not a(n), and not N.

For i in S, strict growth of chronological coding positions gives
a(i)+1 <= a(n)-1. The ordinary code of U is the countable padded
structure's literal prefix of length lev(U). This follows by
forgetting the distinguished vertex of the raw type, taking the
finite-prefix ordinary code, and restricting the complete table.
In particular all absent relations and E atoms are retained.

The actual G+ original at i has size a(i)+1 and its complete code
is a prefix of that ordinary code. The existing fromUpper theorem
gives a genuine strict representing pair with upper U, lower at
level a(i), and vertex equal to the actual original G+ code.
The lower level is in the retained set because the original i is
selected. It is NOT necessary to insert the lower node as a new
seed or assert it belongs to the initial seed set. The covered
upper and retained ancestor lemma from the previous batch supplies
its range membership.

For an injectively labelled q-tuple f, take S = image f, so |S|=q.
One actual bounded-retention envelope covers U. Lift every pair
through this SAME map. The uniform bound is
B(q) = 6*(q+1+(q+1)^2+3*2^(q+1))+1.
The existing bounded-pair/finite-approximation transfer now yields
FiniteGPlusPaletteCovers for the whole set of actual q-tuples, with
one palette depending only on q, not on the ambient indices or
the chosen tuple. Apply the pinned normalized Kpt palette Ramsey
theorem to get a single map and the finite colour bound.

## Adversarial checks

* The fresh cap is included in the envelope budget; requested
  originals alone do not guarantee strict upper endpoint.
* The cap's free cut is a(n)-1. Strictness of padded code positions
  gives the needed two-coordinate margin even for consecutive codes.
* All q tuples use a fixed graph construction; there is no dependence
  of the countable host graph on the colouring or selected tuple.
* The actual pair lower endpoint is not asserted to be a full original
  type. It is an ancestor of the actual cap at a retained level.
* A single envelope acts on a whole tuple. Independent per-coordinate
  maps would not establish palette coverage.
* The actual finite palette includes many non-diaries. Its size
  must NOT be identified with the independently verified 24 histories.
* Sharp comparison requires a legally projected diary to determine
  the actual complete retained graph table and each selected rank.
  The existing one-gap compression theorem then recovers the complete
  finite L+ table. Shape-image retained-code recovery provides the
  inverse source identity. Local canonical-age equality alone is not
  that full graph-table equality.
* An ordinary graph BRD corollary additionally needs the induced
  graph embedding back into the Henson graph, or an equivalent
  G-omega transfer. The new endpoint is deliberately stated at the
  actual G+ tuple level. Unavoidability and the general K_k
  constructor remain separate.

## Validation status

The previous integration's full build failed at Kk.lean, because
two imports had been inserted after its module docstring. The CI log
explicitly reports successful compilation of ResolvedFairCriticalRetention.
This fixes the import placement and adds the actual-prefix palette
candidate. The exact integration build and central axiom audit are
required before these new results can be called Lean verified.
The 24-history enumeration was verified separately in PR #504.
