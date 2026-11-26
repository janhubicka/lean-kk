# Selected class ages pull back to the actual TOP-name list

Date: 24 November 2026. Independent application audit of the existing theorem
`Kk.finiteOldColumnCanonical_reindex` in
`Kk/PhysicalCanonicalSortTransport.lean`, at published baseline
`ddb01a336e60d51ce0db289f0c3ab327a14635d8`.

## Exact existing theorem

For a finite old base pool P, actual Boolean edge table E, complete class
columns `c : Nat → Fin d → Bool`, and **any** map
`pi : Fin e → Fin d`, the checked theorem proves, for `ell>0` and every
admissible nonempty support U,

    canonical_e(raw(E,P,c∘pi))(U)
      = canonical_d(raw(E,P,c))(pi[U]).

No injectivity, surjectivity, symmetry or raw-age consistency is assumed.
The image support remains nonempty and has cardinality no larger than U.
The physical old-column raw bound supplies the support monotonicity required
by the underlying `integerGraphAgeCanonical_pullback_mono` theorem.

This is the full canonical identity, not merely the raw common-neighbour
identity. Its proof sums child weights in each parent fibre. In the reverse
direction it puts the whole parent weight on one chosen representative in
the requested child support. A parent multiplicity is never copied to all
children. The proof discards zero-weight children before using a preimage as
an admissible support; it does not assume an arbitrary support preimage has
size at most ell−1.

## Actual TOP columns and local agreement

Let `j : Fin e → Nat` list the actual eligible selected TOP bases. Suppose
their class assignment pi satisfies

    E(p,j(t)) = c(p,pi(t))   for every p≤b and every t.

Only this local agreement is needed. For either P=range(b) or
P=range(b+1), the actual common-neighbour pool is

    {p∈P : for every t∈U, E(p,j(t))=true}.

Replacing its column by `c(p,pi(t))` gives the identical finite set, since
the defining filter reads no p outside P. Therefore its clique capacity,
raw bound on every support, and canonical age are identical. No assertion
about columns at unprocessed future bases is required.

Apply the existing pullback identity separately to the two finite prefixes.
Equality of the complete class canonical ages then gives equality of the
actual TOP-list canonical ages on every support. This is exactly the finite
dimension-change step required before
`numericHTop_prefix_canonical_ages_eq_of_base_neutral` and the actual chosen
B3 argument. Repeated TOP names or several different TOP names in the same
old class do not create an extra hypothesis. Restricting to a subset of
classes is also included by the arbitrary map pi.

## Changing class domains at an event

One must not identify raw global class indices across a split or a coding
without the construction's actual class correspondence. If the before and
after global domains differ, apply the theorem separately with maps pi0 and
pi1 from the same actual terminal list, and use the known class-age transport
on the two image supports. Equivalently, first identify the surviving
selected classes as prescribed by the selected record, and then use a fixed
class domain. The actual terminal columns `E(p,j(t))` provide the common
labelling on both sides.

An omitted split has only one occupied selected child; its selected class
is identified with the parent. Nonselected coding retains the survivor
classes. Auxiliary cover blocks are attached to unions of the current
classes. These are the concrete class correspondences to check when
instantiating the ordinary resolved-Q construction.

## Conclusion and limits

The existing checked arbitrary-map theorem fully discharges the abstract
canonical pullback step, including repeated labels, omitted classes and
all simultaneous support constraints. A further generic wrapper is not
needed to justify that inference. The exact construction must still supply
the actual class assignment, the local physical column identities and the
appropriate before/after class-age equality. This audit establishes none
of those construction data by assumption and makes no global B3, run or
characterisation claim on its own.
