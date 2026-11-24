# Independent review: actual level maps enumerate retained slots

24 November 2026. Reviewer: generation-zero validation agent.

Reviewed proposal: `docs/retained_level_enumeration_english_20261124.md`.
Reviewed SHA-256:
`f6bb4614b20f06abf734e351e4e128290aac3c76556ca128bd9fb55958e63875`.

## Verdict

The proposed argument is correct and may be implemented. It derives both
the source length and the literal source-coordinate map from actual range
data and a represented endpoint. Neither source size, equality of recovered
codes, nor a proposed level-map enumeration is taken as an input.

This review concerns the English proof and its existing source APIs; it
makes no claim that the new implementation has compiled.

## Ordered-range argument

Two strictly increasing maps from finite initial segments have injective
finite ranges. Equality of these ranges therefore gives equal domain
cardinalities. After the corresponding finite-index transport, uniqueness
of the increasing enumeration gives pointwise equality. The proposal
correctly separates the cardinality step from the same-domain uniqueness
step; a rigidity theorem must not be applied before the domain transport.

For the endpoint statement, the appended list has length `M+1`. Its last
value is the endpoint `tau`, which is distinct from every ordinary slot by
the strict bounds. The restricted numerical level map has length `n+1`.
Its range is exactly the full numerical range through `tau`: if
`lambda(j)<=lambda(n)`, strict monotonicity forces `j<=n`. Thus exact range
through the endpoint really does identify these two finite ranges, giving
`n+1=M+1`, hence `n=M`, and then all ordinary coordinate identities. The
endpoint is counted once in both ranges and excluded from the recovered
ordinary socle.

## Actual Kpt and full-code scope

Checked the existing statements in `LevelRemovalSkipsOnly`,
`ShapeMapFullRecovery`, `GPlusRetainedCodeRecovery`, and
`GPlusCanonicalCodeReconstruction`. For any actual Kpt `ShapeMap`, they
provide strictness of `kptShapeLevelMap`, its exact value at the level of an
actual source cap, and its equality of numerical range with `F.levelRange`.
Consequently the equation `F(U*)=U` supplies the genuine represented
endpoint required by the ordered-range lemma. No surjectivity of an
arbitrary shape map or unexplained preimage is inferred.

The existing `shapeMap_recovers_ordinaryCode` theorem gives the whole source
ordinary finite code by reindexing the target code along
`retainedSocleIndex`. Its coordinates are definitionally the actual level
map. The newly derived source-length equality permits the exact
`FinitePartialCode.reindex_change_size` transport, and finite-index
extensionality identifies its reindex map with the slot map. This recovers
all four tables, including absent binary atoms and directed E. It does not
assert equality of distinguished raw Kpt types.

The Plan-to-slot-range equality and the actual cap image equation remain
explicit inputs of this bridge. They are precisely the duties supplied by
the exact Plan theorem, construction-specific retained slot description,
and actual envelope coverage. Comparing the two physical code tables is
then the separate retained-chunk calculation.

## Boundaries

The proof works for an empty ordinary list. In that case the range through
the represented endpoint consists of that endpoint alone and strictness
forces source length zero. If `tau=0`, the strict slot bounds force the
list to be empty; an anchor cannot simultaneously be an ordinary slot and
the endpoint. No positive-size G+ vertex is concluded in this boundary
case.

No equation `lambda(0)=0` is required. The finite-range argument works even
when the least retained level is positive. In the positive-cap manuscript
application the anchor belongs to the concrete slot list, but that is an
application fact rather than an unnecessary assumption of the generic
lemma. Different occurrences may have different physical slot coordinates;
each level map is identified with its own increasing list before the
common-tag table theorem compares them.

## Source fidelity review

Read `Kk/RetainedLevelEnumeration.lean` in full after the English checkpoint.
All four public endpoints implement the approved statements. The first
derives domain size from actual range cardinality. The second appends the
endpoint on both sides, proves the exact bounded range of the actual strict
level function, derives the length equality, and only then applies
uniqueness of increasing finite enumerations. Its input is range equality
through the represented endpoint, not an assumed coordinate map.

The actual Kpt wrapper keeps both the genuine cap image equation and exact
level range. It derives source length and all coordinates using the checked
Kpt numerical level-map facts. The final endpoint uses the resulting length
equality in the dependent finite-index cast, identifies coordinates by
`Fin.ext`, and applies the complete ordinary-code recovery theorem. No
source-size, retained-map identity or code-equality premise has been added.
The empty list and zero endpoint remain admitted, with no positive-size G+
claim. No mathematical discrepancy was found. This is a source semantic
review, without an independent compilation claim.
