# Independent review: chosen marked B3 from exact TOP reference ages

Date: 24 November 2026. Reviewed before implementation:
`docs/selected_top_age_neutral_b3_english_20261124.md`.

SHA-256 of the reviewed proposal:
`2c35cb5439a6680618a809d332e26228352a72c7d7f19b4c296c90e0a9098e80`.

The proposed finite mathematical implication is sound. Approval is for the
stated reduction from exact actual reference-age equality and genuine chosen
complete upper-type coverage. This does not establish those premises for the
resolved-Q construction or complete the global characterisation.

## Capacity comparison

At c=p(b,g), g<k, every generation of each base q<b is strictly before c.
Every physical edge from any such generation to a displayed later TOP has
the prescribed Q-column bit. The TOP-to-TOP clause is included; omitting it
would lose the simplest lower-capacity witness. Complete TOP copies already
give an induced copy of the old base graph. The verified complete-real-pool
capacity theorem supplies precisely this comparison.

For a nonempty sort support, a positive common neighbour in the numerical
prefix cannot be odd, since odd coordinates have zero ordinary bits. Real
coordinates at most c decode to bases at most b. Any numerical clique
projects to a Q clique on distinct bases: two generations of one base are
nonadjacent, and every directed positive numerical atom projects to the
corresponding base atom. Thus neither repeated generations nor odd coordinates
increase the common-neighbour capacity above its Q-before/after bounds.

The resulting raw-allowance inequalities have the orientation given in the
proposal. Monotonicity of canonicalization gives

    F_Q(after) ≤ F_H(through c) ≤ F_H(before c) ≤ F_Q(before).

Equality of the two outer **canonical** ages therefore forces equality of
the two inner canonical ages. Raw bounds need not coincide, and equality of
raw and canonical functions is not assumed. All admissible nonempty support
constraints are required. For the fixed K4 language these suffice for every
future clique, including those with repeated sort labels.

## Application to the actual chosen continuation

In a finite ordinary failure witness, cover each genuinely chosen future
complete upper L-type by one displayed TOP original. Give that future vertex
the corresponding sort. The labelling need not be injective, and choosing a
sort does not alter future-future edges. Complete type equality fixes both
directions and both Boolean values of every old/future ordinary atom, as well
as the relevant unary and diagonal facts. The old socle is the same actual
initial numerical graph throughout.

After deleting c, forbidden-freeness is therefore exactly admissibility of
this finite labelled future graph over the before-c prefix. The actual
finite-old/future reference-age theorem expresses this by all canonical
support constraints. Equality of the physical before/after ages transfers
the constraints, and the reverse implication of that theorem makes the
undeleted continuation forbidden-free, contradicting the alleged failure.

The argument requires no auxiliary E relation on this arbitrary ordinary
continuation. Actual E eligibility belongs to the source/type extraction, not
to an artificial enrichment of the finite age witness. It also requires no
no-I2 premise for the marked-only assertion. The separate full-source transfer
still needs whatever no-I2/representation hypotheses its theorem states.

The empty-source endpoint is harmless: any failure involving the restored
coordinate must also have a future vertex, because the actual old numerical
graph is forbidden-free. Such a vertex cannot have an allowed chosen type if
there are none. An implementation can use the existing empty-source result
or retain this case in the direct finite-witness argument.

## Checked boundary example

The two-sort example in the proposal is valid. Nonadjacent old bases with
columns (1,0) and (0,1) give singleton capacities 2 and mixed canonical
capacity 3. Adding a nonadjacent old base with column (1,1) keeps the two
singletons at 2 but lowers the mixed capacity to 2. A future triangle with
labels x,x,y is compatible before the new base and forms K4 with it afterward.
Selected no-split can hold in this example. Consequently singleton neutrality
and structural no-split cannot replace full age equality in the B3 argument.

## Requirements to retain in Lean

The displayed TOPs must be actual finite originals, with explicit carrier
bounds p(j_t,k)<N and later bases j_t>b. The chosen-output premise must cover
the exact complete upper L-types selected by the actual prescribed function,
not just equal singleton ranks, positive cut bits or separately available
representatives. The old-prefix pools must include every ordinary coordinate
before/through c. The finite failure witness and deletion reindexing must
retain the same old socle and unchanged future graph. Repeated labels and
empty finite supports must be handled by the precise domains of the existing
reference-age theorem. Off-plan construction, whole-stage Plan inclusion and
the chosen-type application remain separate until actually instantiated.

## Initial chosen-B3 implementation fidelity review

The independent reviewer read the initial `Kk/SelectedTopAgeNeutralB3.lean`
implementation against the proposal and its imported failure/reference-age
theorems. Its finite-pool avoidance helper first derives zero diagonal from
loop avoidance and then realizes the forbidden clique in sorted order. The
finite future pool contains all bounded future carrier vertices, and its
sort assignment permits repetitions while leaving future-future edges
unchanged. Both old/future edge directions come from the genuine complete
chosen type equality. The old raw-bound transports use equality on the
same full before/through-cut physical socles. The empty sort case uses
actual coverage to exclude eligible selected names and invokes the existing
no-positive-neighbour B3 result. No source-level mathematical mismatch was
found; this review does not claim compiler or axiom execution.


## Cut-visible strengthening and whole-stage wrapper: source review

The independent adversarial reviewer subsequently read the strengthened
`Kk/SelectedTopAgeNeutralB3.lean` and the new
`Kk/ResolvedQNeutralAgeB3.lean`, together with the exact existing
`henson_failed_selectedB3_has_exact_full_cut_star_core` statement and proof,
the lower-real physical decoder, and the bounded genuine-stage role theorem.
The strengthened implementation matches the separately reviewed English
checkpoint `cut_visible_neutral_age_full_b3_english_20261124.md`.

The new `hCover` applies only to selected, genuinely eligible, positive
physical cut-neighbours. This is sufficient because the extractor trims the
future carrier to one forbidden clique core while retaining the entire old
socle. Every future point of this same core has one physical label carrying
all three facts and equality of its complete chosen next ordinary type.
The implementation applies coverage to that exact label, not to a different
old-equal representative. The finite future pool still includes every future
carrier point of the extracted V. Both ordinary directions, all negative
old/future bits, arbitrary future edges and repeated labels are unchanged.
No extra no-I2 or marked-output-fibre premise is needed.

For an empty target list, the source may still contain negative cap or
auxiliary names. Coverage rules out precisely the positive eligible names,
and the existing no-eligible-cut-neighbour theorem proves B3. This is the
appropriate empty case for the stronger statement; it does not assume an
empty selected stage.

The resolved-Q wrapper uses the literal full stage
`hStageOriginals(K,k,N,U,J)` and allows any selected predicate on that stage.
The physical decoder provides a later base, a bounded real generation and
the actual positive base edge. The corrected role theorem consumes these
canonical bounded addresses and the genuine descending inclusion
`J ⊆ Plan`, deriving the selected-coded TOP role. The target carrier bound
is then obtained from the original `Fin N` name itself. Target coverage
supplies a matching base, so the complete physical target type is unchanged.
All Plan/root role contracts retain `m ≤ k`; the numerical address-alias
vacuity repaired in the earlier audit is not reintroduced.

The target coverage premise asks for every later selected-coded base whose
TOP lies in the finite carrier. Such a list is finite; repeated entries and
extra later targets are harmless but strengthen the neutrality premise.
No source-equality, chosen-B3, structural exclusion or no-I2 verdict is used
as an input. The full actual base-age equality and descending stage/Plan
realization remain concrete construction obligations. The wrapper concludes
B3 for genuine stage prescribed data, not the full AlgorithmRun boringness
or global characterization theorem.

No mathematical mismatch was found. This is a source-semantic audit only;
the parent agent owns compilation and transitive-axiom checks. During this
review, the two reserved `prefix` binders in
`NumericTopNeutralPrefixAge.lean` were renamed to `prefixBound` with no
change to the mathematical statements or capacity argument.
