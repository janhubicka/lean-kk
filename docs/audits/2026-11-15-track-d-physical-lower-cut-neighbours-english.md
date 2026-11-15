# Track D — exact physical positive cut-neighbour classification below top

15 November 2026. English-first mathematical proof and hostile audit
BEFORE Lean code.

## Exact theorem

Let B be an arbitrary Boolean directed binary table in the normalized
signature and let k be the numerical-H height. Consider an ACTUAL
real physical cut c=hPosition k i g with g<k, and any L-vertex y
strictly later than c. If hNumericBinary B k c y t is true
for some binary symbol t, then there are j,m with:

    i < j,       g < m <= k,
    y = hPosition k j m,      B i j t = true.

The reverse implication is also valid when y is that exact
higher-generation real address: since g<m, the literal generator
gate opens and its directed H atom equals the actual directed
base atom B i j t.

This is a precise characterization of positive physical cut
neighbors, NOT a statement about arbitrary future vertices of
an L-only corrected-B3 age witness.

For the actual finite Henson numerical H(E,k,N), a cut c<N,
and a genuine original v:Fin N AFTER c, the same equivalence
reads:

    L_H(c,v)=true
    iff exists j,m: i<j, g<m<=k, v=hPosition k j m,
                       E(i,j)=true.

Further, if v is cut-eligible by
`c+1 <= finiteNumericH.freeLevel(v)`, the checked ambient
freeLevel<=physical-address theorem automatically gives c<v.
Thus the no-separate-address-premise corollary classifies ANY
actual eligible, physically cut-adjacent selected original name
by a strictly higher numerical generation and later BASE.

No no-(I1)/(I2), marked source nonempty, selected graph-age,
E-parameter closure, or common source orbit is required.
It works for arbitrary Boolean B, not just symmetric graph E,
in the raw physical relation theorem.

## English proof

Unfold the checked `hNumericBinary_true_iff`: a true atom
has one exact generator with base indices u<v, bounded
generations q,n, the generation gate
`q<n OR (q=n=k)`, and one of two endpoint orientations.

**Forward orientation.** We have:
`c=hPosition k u q`, `y=hPosition k v n`,
and B(u,v,t)=true. The REAL physical cut has
`c=hPosition k i g`, g<k. By the already kernel-checked
`hPosition_injective_bounded`, bounded real positions
are injective, so i=u and g=q. Since g<k, the special
top/top equality case q=n=k is impossible. Hence
g=q<n=m<=k. Set j=v, m=n, and substitute i=u
into the base atom.

**Reversed orientation.** The generator would place
c=hPosition k v n and y=hPosition k u q with u<v.
But `hPosition_lt_of_block_lt` says the smaller base
has strictly smaller numeric position, so y<c,
contradicting the assumed c<y. This uses the physical
ordering, not an arbitrary application of symmetry.

**Converse.** For i<j, g<m<=k, the checked
`hNumericBinary_real_forward_iff` says the actual
directed atom equals B(i,j,t) since the allowed gate
g<m holds. Rewrite y to its prescribed H position.

**Actual Henson cut-eligible corollary.** The checked
finite numerical-H `freeLevel_le` gives
`freeLevel(v)<=v.val`. With `c+1<=freeLevel(v)`,
obtain `c<v.val` and invoke the exact forward theorem.
No extra selected-source/closure hypothesis is introduced.

## 17 hostile checks

1. The source cut is PHYSICALLY real at generation g<k.
   An arbitrary reindexed Kpt source level is not such a cut.
2. The strict later address condition c<y is essential
   to rule out reverse numeric generator orientation.
3. The input g<k is essential to eliminate the permitted
   special top-to-top gate q=n=k.
4. If g=k, positive later neighbors need not be higher
   generation; the theorem would be false.
5. The generator may be asymmetric. The theorem reports
   exactly B(i,j,t), never mistakenly B(j,i,t).
6. Only positivity of one specified binary symbol is
   classified. All other negative atom comparisons still
   matter for corrected B3 chosen upper types.
7. No E auxiliary predicate appears in `hNumericBinary`;
   it is the ordinary-L reduct, not numerical H+ E.
8. Odd fake coordinates are excluded as a consequence of
   positive L, not silently assigned a generation.
9. Same-base numerical copies have no ordinary pair;
   the true generator always has i<j.
10. `hPosition_injective_bounded` requires q<=k and g<=k,
    both explicitly justified by the generator and g<k.
11. No source selected-active-branch equality is assumed:
    the v is an arbitrary actual physical original address.
12. The finite model has carrier N, so using v:Fin N
    is necessary for a genuine name in the actual prefix.
13. Numerical H `freeLevel_le` is used ONLY on the real
    finite actual structure, not on an abstract free E witness.
14. The cut-eligible selected original can be an auxiliary
    full parameter (q2-like) rather than a selected diary
    macrobranch. The theorem does not erase it.
15. Uniform equality of COMPLETE chosen upper L-reducts
    is still needed for the finite B3 marked-to-full
    transfer; classifying generation/base alone is not enough.
16. The small-independent upper must prove by actual
    Q-block schedule that all higher-generation cut-adjacent
    full closure names are in the represented marked source
    or have equal complete chosen target type.
17. Kernel compilation + strict named transitive-axiom
    reports must pass before the paper marks this finite
    physical edge theorem verified.

## Proposed Lean implementation

New `Kk/PhysicalLowerRealCutNeighbour.lean`, import
`Kk.NumericPrefixGapZero` and `Mathlib.Tactic`.

Three endpoints:
- `physical_lower_real_cut_positive_generators`:
  any true ordinary H atom from c=hPosition k i g,
  g<k, to later y arises at later base/higher generation.
- `physical_lower_real_cut_positive_iff`:
  exact two-sided Boolean atom equivalence for the above
  generator representations.
- `finiteNumericH_eligible_lower_cut_neighbour_is_higher`:
  any genuine finite original v whose free level reaches
  cut+1 and whose physical ordinary-L adjacency to the
  cut is true has j>i,m>g and E(i,j)=true.

Dedicated exact-head build and strict three-qualified-theorem
axiom gate. This is one finite geometric lemma needed in the
actual omitted even cut-source B3 proof, but not the full
boringness theorem or a global big Ramsey degree statement.
