# Chronological round enumeration of the actual fair limit

## English proof before implementation

Write P_n for the actual finite old pool at stage n. These pools
increase. The coded original 2n is live at stage n, hence is not in
P_n, and it belongs to P_(n+1). Therefore
D_n=P_(n+1) minus P_n is a nonempty finite set containing 2n.

List the elements of D_n other than 2n in increasing numerical order,
then append 2n. This is a nonempty list with no repetitions, containing
exactly D_n and putting the code last. For n<m, the whole of D_n
already belongs to P_m, whereas D_m avoids P_m. Thus distinct batch
lists are disjoint.

When P_0 is empty, induction gives the exact equality
union_(m<n) D_m=P_n. Apply the independently proved positive finite
batch schedule. Its chronological vertex map e is injective, its
range is the actual limit domain, and its prefix ending at the n-th
batch boundary has exactly vertex set P_n. These facts are constructed
from the actual fair stages, not assumed of a proposed enumeration.

The position of 2n is the final tagged entry of batch n. The tagged
inverse property gives e(position(n))=2n. Batch intervals are ordered,
so position is strictly increasing. Pull back the limit graph along e.
Injectivity sends each finite clique to a finite clique of the same
cardinality in the limit. The pullback is therefore K4-free and its
increasing coded positions induce the prescribed original graph.

## Precise scope

This orders whole rounds and places the actual coding vertex last in
each round. It proves exact old-prefix sets. It does not order the
separate marker and cover events inside the sorted extras, or prove
that each such auxiliary block is consecutive. Those finer event
records must still be extracted from the finite round traces. In
particular, this is not yet the complete one-gap diary parser or the
occurrence-independent inverse-source theorem.

The empty initial old pool is explicit when identifying the range and
prefixes. No initial vertices are silently discarded. Every round
is nonempty because its fresh even original is coded, including when
there are no auxiliary extras.

## Local validation

`Kk.ResolvedFairChronological` passed its normal serialized local Lake
target on the pinned Lean 4.35.0-rc3 toolchain. Its single elaboration
repair explicitly identifies the chronological map before transporting
membership along an equality. The downstream
`Kk.ResolvedFairOneGap` target also passed. The full project build and
named transitive-axiom checks are recorded in the batch integration
evidence.
