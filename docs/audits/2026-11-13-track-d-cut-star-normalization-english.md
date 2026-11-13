# Track D — canonical cut-star normalization of corrected (B3)
13 November 2026. English-first proof and adversarial audit, before Lean.

## Target theorem

Fix a symmetric loop-free K_ell-free Boolean base graph E (ell >= 2),
its actual finite numerical H partial structure A with k satisfying
ell <= k+1, a cut p<N and a finite pool of genuine original names
original : Fin M -> Fin N. Let Full be a name predicate representing
ACTUAL nodes in one parameter-closed Kpt set Z strictly above p.
Assume no two nodes of Z in a common component have meet at p.

Define the **canonical cut-star selection**:

  Star(v) := Full(v) AND A.L.binary p (original v) 0 = true.

Then, with the source functions constructed by the actual
selectedStagePoolPrescribedData:

  CorrectedB3(Full)  <->  CorrectedB3(Star).

No separate assumption that Star is nonempty is needed.

This equality is for two predicates on names in the SAME genuine
finite numerical H, with the SAME tested p and closure Z. It is not
an identification of the macrodiary's active names with Star.

## Lemma 1 (failure forces a real selected cut neighbour)

If CorrectedB3(Full) fails, some v has all three properties:

  Full(v);
  p+1 <= A.freeLevel(original v);
  A.L.binary p (original v) 0 = true.

Proof. The checked theorem
henson_selectedB3_failure_has_clique_witness gives an L-only bounded
continuation W preserving the complete actual old L-socle through p,
whose deletion of p avoids the normalized Henson forbidden family,
whose upper vertices have complete next-cut L-types of cut-eligible
Full-named actual originals, and which contains a forbidden K_ell.
Apply the checked normalizedForbidden_bounded_signature_cut with the
real H-free old socle and the same forbidden clique. The result
indexes the forbidden clique with r lower vertices, 0<r<ell, whose
last lower vertex is exactly p and whose first upper vertex e(r)
satisfies p<e(r). The clique edge W.binary p (e(r)) is true.
The type of e(r) is the full (p+1)-type of some genuine Full-named
original v with p+1<=freeLevel(original v). Equality of full prefix
types includes that directed crossing atom, so the actual H edge
A.L.binary p (original v) is also true.

No arbitrary upper--upper W edge is identified with an actual H edge;
only the single p-to-upper crossing is used.

## Lemma 2 (nonempty Star case)

Suppose Star(v0) for some v0. By genuine Full representation above p,
v0 is cut eligible. Every Star name represents a node of Z, and
no-(I2) forces COMPLETE next L+ source-fibre coherence. The verified
Track D theorem
henson_fullB3_of_no_i2_marked_closure_cut_neighbours
can be applied in BOTH directions:

- Full <- Star: all eligible cut-adjacent Full names are in Star by
  its definition, and Star is nonempty.
- Star <- Full: Star is included in Full, and Full is nonempty.

Both transfers are on one actual H and one Z; the same original-name
family and no-(I2) hypotheses apply. Consequently the two B3 tests
are equivalent.

## Lemma 3 (empty Star case)

Suppose no Star name exists. If Full failed corrected B3, Lemma 1
would produce a cut-eligible Full name with positive actual edge to p,
contradicting emptiness. Thus Full passes. Star's source is empty
because it has no selected name, so its corrected B3 is vacuously
true. This proves the equivalence without any arbitrary special
default source or fabricated upper type.

## Hostile audit: distinctions that cannot be erased

1. The normalization is NOT to the user's original selected active
   macrodiary. Star may include auxiliary parameters. The literal K4
   q2/x microevent requires precisely such an auxiliary type.
2. A source name cannot be kept merely because its positive L
   crossing matches. The *complete* p+1 L-reduct is retained.
3. The complete old **L+** type is used for fibre coherence; mere
   ordinary L-socle equality is not enough to identify Kpt ancestors.
4. Without no-(I2), deduplication of old sources may choose
   different next types in Full and Star, so equivalence can fail.
5. A failure can produce an upper clique vertex even if most of its
   future vertices are unnamed by Star initially: the checked
   forbidden signature ensures 0<r<ell and selected type names.
6. Full source may be empty; then both sides trivially pass. The
   empty-Star case must not use a nonempty-source transfer theorem.
7. No E relation is imposed on the arbitrary L-only age-test W.
8. The theorem is finite, actual H, single cut and single closure Z.
   It does not synchronize two different occurrences or give
   common inverse-source Kpt equivariance.
9. It does NOT discharge the manuscript's separate full corrected
   B3-loss <-> relative graph-age loss hypothesis. A finite normal
   form does not prove relative fixed-source realizability.
10. No unconditional exact big Ramsey degree or lower-bound result
   follows. Keep manuscript global pending markers.
11. For the paper, the correct new **candidate invariant** is
    the multiset/set of complete L-reduct output types of Star,
    not only the selected diary's F-function.
12. Edit only olive manuscript prose. Black text is frozen, and
    existing removed TODOs must not be restored.

## Lean test contract

Create a separate new module importing
Kk.B3ClosureFibreCoherence and Kk.HensonZeroGenerationClique.
First prove the failure-forces-selected-cut-neighbour lemma with
actual normalized forbidden signature; then prove total equivalence.
Compile new module and run strict named transitive-axiom reports on
its exact head (only propext, Classical.choice and Quot.sound).

No newly proven conditional statement should be promoted to a
global manuscript green marker. Full CI and paper TeX need separate
validation.
