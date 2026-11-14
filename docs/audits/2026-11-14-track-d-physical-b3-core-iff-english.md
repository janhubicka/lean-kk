# Track D — exact finite PHYSICAL cut-star obstruction iff failed corrected (B3)
14 November 2026. Mathematical English proof and hostile audit BEFORE Lean.

## The new converse, not a graph-age theorem

The verified Kk.B3ExactCutStarWitness theorem gives a necessary compact
physical cut-star clique for every failed genuine selected-stage
corrected-B3 test. The logical converse is delicate: a physical original
with an eligible full next-cut ordinary-L type need NOT be the selected
prescribed map's CHOSEN target when two originals share the same old full
L+ source. A literal K4 q2/x example already warns against discarding
auxiliary types.

We derive a genuine equivalence, under the *same physical closure*
representation and no-(I2), and make its precise limits explicit.

Fix ell>=2, ell<=k+1, a symmetric loop-free K_ell-free E,
A=finiteNumericH(normalizedGraphModel E,k,N), p<N, a finite original-name
carrier original:Fin M -> Fin N, a Selected predicate, and a true set Z
of Kpt closure nodes. Every Selected name represents a node in Z
strictly above p and below that actual Kpt original; there is NO pair
in Z with a common component and meet at p.

Define a PHYSICAL BAD CORE to be a finite ordinary-L AgeTestModel V with:

* a complete old ordinary L-socle identical to A.L through p;
* deletion of p avoids the entire normalized Henson forbidden family;
* an induced K_ell clique e containing p;
* every vertex of V above p belongs to this ONE clique;
* for every such upper vertex x there is one genuine Selected original
  v that simultaneously has p+1<=A.freeLevel(original v),
  positive A.L adjacency from p, and equality of the COMPLETE directed
  L prefix-type of x with the actual original at p+1;
* at least one genuine Selected original is cut-eligible, giving a
  genuinely nonempty prescribed source (rather than a vacuous B3 test).

The last condition is explicit to avoid silently inferring that an
arbitrary hypothetical clique has an upper vertex: a forbidden clique
copy might be wholly in a presented initial socle if source avoidance
were not tracked properly. In the necessary direction the checked
failed-B3-to-selected-cut-neighbour theorem supplies the seed.

**Claim:** Under genuine Selected closure representation and no-(I2),
the full selected-stage corrected B3 fails iff such a physical bad core
exists. The equivalence is at a SINGLE cut in ONE numerical H; it says
nothing about a macrodiary's selected F function.

## Necessary direction: failed B3 -> core

Invoke Kk.henson_failed_selectedB3_has_exact_full_cut_star_core:
it supplies one finite bounded V and e with exactly the properties of
old-socle, deletion avoidance, forbidden copy containing p, all upper
vertices belonging to e, and each upper vertex's genuine full-name
eligibility + physical cut edge + complete L-prefix type.
Invoke the already checked
Kk.henson_failedSelectedB3_has_eligible_cut_neighbour
to obtain an explicit nonempty eligible Selected name. Package them.

No no-(I2) premise is needed in this direction.

## Sufficient direction: core -> failed B3

Let F=selectedStagePoolPrescribedData A p original Selected.
Use the explicit eligible Selected seed v0 to put the *actual* complete
old L+ type T0=A.partialTypeAt p (original v0) in F.source.
The checked selectedStagePoolPrescribedData_source_original supplies
an eligible actual original u0 whose complete assigned output equals
F.target T0. The common ordinary-L socle of this actual chosen output
is the ambient A.L socle, including both orientations and negative
atoms (ambient_partialType_prescribedSocle). Since V has the same old
socle, V matches precisely prescribedOrdinarySocle(F.target T0).

Now consider each x above p in V and its named physical v from the
core. The complete old source T_v=A.partialTypeAt p(original v)
belongs to F.source because v is genuine Selected and free-cut eligible.
The chosen representative w for T_v need not be v! However
Selected(v), Selected(w) both genuinely represent nodes of the SAME
Z above p, their complete old L+ types agree, and no-(I2) applies.
The verified Kk.kpt_marked_next_full_type_eq_of_no_meet therefore
gives equality of the COMPLETE next L+ records for w and v.
Consequently the complete next ordinary-L reduct of the actual v
is a PERMITTED F.PrescribedUpperLType, even after source
deduplication and arbitrary chosen target selection.

Therefore V is a finite CommonSocleAgeTest candidate for F at source
T0, with *every upper L-prefix type in the chosen output family* and
deletion of p still in the age. But V realizes K_ell, one of the
normalized forbidden family. If F.CorrectedB3 held, it would assert
V avoids every forbidden pattern, contradiction. Thus F fails B3.

This proof never imports future-future edges of V from E, or equips
V with any auxiliary E data.

## Hostile checks

1. Do not assume Selected is the full closure-selected source without
   a representation argument; here explicitly require
   Selected(v) -> closureSelectedOriginal(... Z p v).
2. Do not assume no-(I2) from selectedness: it is an independent
   hypothesis at exactly the same Z and p.
3. The chosen representative of an old source may differ from v;
   prove the fibre-coherent next L+ equality rather than using
   membership alone.
4. The old FULL L+ source must agree for the fibre lemma, not merely
   the common ordinary-L socle.
5. The B3 age witness is L-only. Auxiliary E does NOT exist there.
6. Upper-upper edges of V can be arbitrary. Only old-to-upper complete
   L prefix types of genuinely chosen originals are compared.
7. Never discard negative incoming or outgoing L bits, loops, unary
   or diagonal atoms.
8. Seed nonemptiness must be actual selected AND free-level eligible,
   not a nonempty arbitrary index set.
9. The normalized Henson family includes forbidden singleton and
   asymmetric signatures. Their absence from the certificate follows
   from the checked clique-core reduction for genuinely symmetric H,
   including generation zero.
10. For a hypothetical certificate containing a K_ell clique, the
    family member actually forbidden must be exhibited in Lean.
11. The core's upper vertices are all in ONE K_ell image; there can
    be at most ell-1 of them, but original labels may repeat.
12. The theorem is finite and single ambient; no pairwise equality
    of B3 profiles across two independent occurrences is asserted.
13. The result does NOT identify physical source types with selected
    active macrodiary branches; q2-like auxiliary types stay present.
14. It does NOT establish that a lost normalized support vector for
    the selected-front graph age is equivalent to this physical core.
    That would require fixed-source relative realization/fidelity.
15. A false shortcut is to assume the already checked finite universal
    ordinary-L future realizes arbitrary forbidden cliques over one
    fixed old Henson prefix. It does not.
16. No global GREEN manuscript marker or exact BRD count is promoted.
17. Compile the new module on the exact pinned successor-library
    and check named transitive axioms, no sorryAx. Do not alter
    existing black manuscript text or centrally merged proof bodies.

## Lean endpoints

A. General same-closure lemma:
  selected_named_nextL_permitted_of_no_I2
on an arbitrary enumerated partial L+ structure A, explicit family,
hAvoid, Z, Selected genuine closure representation, hNoI2; one
Selected+eligible v -> F.PrescribedUpperLType of the actual next L.

B. Henson finite physical bad-core definition.

C. Exact theorem:
  henson_fullB3_failure_iff_physical_cut_star_bad_core_of_no_I2.
Both directions derive their own inputs from full finite source data.
