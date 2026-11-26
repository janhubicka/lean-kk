# Upper characterisation continuation: exact local lemmas

## Scope and recoverability

The previous local continuation reported successful verification of twenty
modules and 218 named declarations. Its unpublished local commits
`8e1322af09c2a72e214e9c19d04d25b45b4a6c98` and
`b7e3ae46a16f013be4af87eae9b22cd9e2e6548b` were not available when this
workspace was restored. GitHub's current main remains
`0fcac8624ef0328ff4b885b8945e682d480d8669`; the ordinary nonedge semantics
and count remain separately available in draft PR #504. This branch does
not present itself as the missing 218-result branch or as a recovered
complete ordinary lower-bound implementation.

Two small upper lemmas have complete source and English arguments in the
visible continuation record. They are being reconstructed against the
published baseline and will receive fresh kernel and axiom checks. Their
previous mathematical review is retained; no new completed global
characterisation claim follows from either lemma.

## Equal cut bits determine complete next types

Let A be one actual EnumeratedPartialStructure 1 0 1, with symmetric
ordinary binary relation. Let v,w be finite original vertices, both
eligible at cut+1. Assume equality of their complete partial types at cut
and equality of A.L.binary cut v 0 and A.L.binary cut w 0. Then their
complete partial types at cut+1 are equal.

Restricting the two next types recovers the assumed equal old types.
Compare all six fields of CompleteNextColumn. At the distinguished
vertex, the forward ordinary equality is the assumed cut-bit equality;
symmetry gives the reverse ordinary equality. Eligibility makes forward
auxiliary E true and reverse auxiliary E false on both sides. At every
ordinary socle vertex the fields are the same actual ambient entries.
There are no unary relations (Fin 0), and the new diagonal also is the
same ambient entry. Six-field extensionality and
completeNextColumn_determines_type reconstruct equality of the full
next types.

The common bit can be true or false. The local statement applies at
cut zero too. It retains complete old L+/E equality and eligibility; no
selected-age replacement, graph-age hypothesis, no-fork conclusion,
looplessness, or distinctness premise is used. Applying this lemma to
an actual stage still requires a proof that its cut bits agree.

## Auxiliary old-column separation modulo isolated dummies

Let role and E satisfy the existing ResolvedQChronologicalAxioms. Add the
construction property: if two members p<j belong to the same auxiliary
block, each intermediate b is dummy or belongs to that block. This is
convexity after deleting isolated dummy bases; it permits a dummy to be
inserted between two members of one block.

Suppose b<j, b is omitted and non-dummy, and j is a retained auxiliary
original. Then E p j is false for every p<b. Split the role of p. Dummy
isolation, coded-before-auxiliary nonadjacency, and different-block
nonadjacency give three cases directly. If p belongs to j's block, the
interval property puts b in that same block, because b is not dummy.
The common block flag makes b retained, contradicting that b is omitted.

The non-dummy guard is essential. At a dummy base the new cut-star is
zero, but a later auxiliary original's old pool need not be empty. This
lemma does not construct Q/role, prove the interval property for that
construction, or establish numerical no-I1/no-I2.

## Validation obligations

The exact reconstructed declarations, their public imports, and their
transitive axiom reports must be checked on this branch. Only propext,
Classical.choice, and Quot.sound are permitted. New whole-stage geometric
lemmas require their own English proof and independent review before
implementation. The actual Q/Plan construction, positive-cut structural
exclusions, full labelled-source orbit, and upper canonisation remain
separate obligations.
