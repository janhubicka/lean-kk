# Generation-zero coherence from actual old-column singleton neutrality

24 November 2026. English mathematical proof, before Lean implementation.

## Scope and exact new content

This note closes a local mathematical implication that was left open in
`2026-11-23-positive-stage-nonvacuity-and-zero-boundary.md`. It does not
construct the infinite resolved graph, prove the descending Plan invariant,
or establish chosen corrected-B3 or common-source/orbit identification.

The new implication uses two ordinary **base graph** properties of an
omitted event: no split among selected future old profiles, and preservation
of each selected future singleton's **actual finite old-column canonical
capacity**. It derives the old positive witness from the latter property,
then proves complete old-to-next L+/E coherence on the entire eligible
physical stage. No whole-stage coherence, no-I1, no-I2, selected-shadow
identification, or external old-witness premise is assumed.

The role/Plan hypotheses and block interval property are exactly those
already used in the published positive-generation and block-separation
results, with every tested real presentation bounded by `m <= k`.

## Concrete singleton capacity, independent of a chosen front enumeration

For a base graph `E : Nat -> Nat -> Bool`, a future base j, and cutoff b,
let P_b be `Finset.range b` and give the unique sort in `Fin 1` the exact
old column `c_j(p,0) = E(p,j)`. Define

    sigma(E,b,j) = integerGraphAgeCanonical 1 4
      (finiteOldColumnRawBound E 4 1 P_b c_j)
      (trackFSingletonSupport 1 4 0).

All old bases below b are included, including omitted earlier originals,
auxiliary originals, and dummies. This is not a stipulated singleton label.
The checked theorem `k4_canonical_singleton_le_two_iff_old_neighbour`
applies literally to these data and gives

    sigma(E,b,j) <= 2  iff  exists p < b, E(p,j)=true.

Equivalently, the singleton value is `3 - omega(N_b(j))`, where omega is
the genuine finite directed-clique capacity and N_b(j) is the old positive
pool. Canonicalization preserves this raw singleton value; no equality of
all raw and canonical bounds is asserted.

### Lemma A: neutrality supplies a real old witness

Suppose `E(b,j)=true` and `sigma(E,b,j)=sigma(E,b+1,j)`. The base b belongs
to P_(b+1), so the checked equivalence gives `sigma(E,b+1,j)<=2`.
Neutrality gives `sigma(E,b,j)<=2`; the same equivalence now supplies a
base p strictly below b with `E(p,j)=true`.

This proof works at every natural b. At b=0 its conclusion is impossible,
so the premises correctly preclude a newly positive, singleton-neutral
column at the empty old prefix. No loop-freeness, symmetry, K4-avoidance,
or realization-density assumption is needed for this finite implication.

## Exact physical theorem to implement

Fix k>0, N, `A = finiteNumericH (normalizedGraphModel E) k N`, a finite
root-original pool U, a stage level set J, and Plan with `J subset Plan`.
Let `Stage = hStageOriginals (normalizedGraphModel E) k N U J` and let
`name = hOriginalName Stage` be its genuine finite enumeration.

Assume:

1. `ResolvedQChronologicalAxioms role E`, including ordinary symmetry,
   dummy isolation, coded-before-auxiliary nonedges, distinct-block
   nonedges, and same-block retained-flag coherence.
2. The bounded root and Plan role contracts from
   `resolvedQ_stage_name_shape_of_planned_levels`: roots at a bounded
   real presentation have dummy role; positive-free-level Plan names
   are selected coded TOPs or retained auxiliary originals.
3. Auxiliary blocks are intervals modulo dummies, exactly as in
   `ResolvedQBlockSeparation.omitted_nondummy_later_retained_aux_old_column_zero`.
4. The tested base b is non-dummy and `ResolvedQOmittedBase (role b)`.
   Set `cut = hPosition k b 0` and assume `cut < N`.
5. Selected no-split at b: for all j,j'>b with both roles `coded true`,
   equality `E(p,j)=E(p,j')` for every p<b implies
   `E(b,j)=E(b,j')`.
6. Actual singleton neutrality at b: for every j>b of role `coded true`,
   `sigma(E,b,j)=sigma(E,b+1,j)`.

For every pair v,w in **all of Stage** with

    cut+1 <= A.freeLevel(name v),
    cut+1 <= A.freeLevel(name w),
    A.partialTypeAt cut (name v) = A.partialTypeAt cut (name w),

conclude

    A.partialTypeAt (cut+1) (name v)
      = A.partialTypeAt (cut+1) (name w).

The theorem may also state the cut-bit equality separately. The roots,
retained auxiliary originals, and actual selected TOP names are all in its
quantifier; it is not restricted to closure-marked B3 inputs or to strictly
crossing closure nodes.

## Proof on the entire eligible original stage

By the checked `full_equal_ordinary_cut_column_determines_next_type`, it
suffices to prove equality of the two ordinary cut bits. If both are zero
there is nothing to prove. To exclude unequal bits, interchange v,w if
necessary and suppose the cut bit to v is true and that to w is false.

### The positive representative and its old witness

The physical lower-cut neighbour decoder, at generation zero and k>0,
gives a later base j>b, a bounded generation m with 0<m<=k, the exact
address `name v = hPosition k j m`, and `E(b,j)=true`. The existing
whole-stage role classification makes j a selected coded base and m=k.
By singleton neutrality and Lemma A, choose p<b with `E(p,j)=true`.

The actual coordinate `old = hPosition k p 0` lies strictly below cut.
The numerical-H TOP gate is open, so `L(old,name v)=true`. Equality of
complete old types includes equality of this ordinary bit, hence
`L(old,name w)=true` as well. This uses the lReduct and its actual old
coordinate, not a graph-age witness or an arbitrarily assigned auxiliary E.

### Recover and classify the second representative

Eligibility at cut implies eligibility at old. Apply the same physical
positive-neighbour decoder at old to the positive bit into w. It gives an
actual bounded address `name w = hPosition k j' m'`, with p<j', 0<m'<=k,
and `E(p,j')=true`. Thus the second name is a genuine real original even
if no real-address shape was assumed before this step.

The bounded stage-role theorem gives precisely three cases.

* Dummy: ordinary symmetry and dummy isolation give `E(p,j')=false`,
  contradicting its decoded positive bit.
* Retained auxiliary: eligibility implies `cut < name w`. Bounded block
  order therefore gives b<=j'. Equality j'=b would make the omitted base
  a retained auxiliary, impossible by `ResolvedQOmittedBase`. Hence b<j'.
  The checked block-separation theorem, with p<b, gives
  `E(p,j')=false`, again a contradiction.
* Selected coded TOP: m'=k. We must also verify j'>b; mere numeric address
  order is not enough for this case. Since p<j', j'>0. The exact literal
  free-level theorem gives

      A.freeLevel(name w) = hPosition k (j'-1) k + 1.

  If j'<=b, the old-block order puts `hPosition k (j'-1) k < cut`, making
  this free level at most cut, contrary to eligibility at cut+1.
  Consequently j'>b.

This exhausts the entire stage. In particular, an eligible fake name cannot
survive the positive old bit, and a same-base selected TOP cannot be treated
as a later source merely because its numerical address exceeds cut.

### Selected no-split finishes the ordinary bit comparison

Both v and w are now actual selected TOPs at later bases j,j'>b. For every
q<b, the coordinate `hPosition k q 0` lies below cut, and its two ordinary
TOP bits are exactly `E(q,j)` and `E(q,j')`. Equality of complete old types
therefore gives equality of the entire old base profiles. Selected no-split
forces `E(b,j)=E(b,j')`. The two generation-zero-to-TOP gates are open, so
the physical cut bits are equal, contradicting the assumed true/false pair.

Finally, ordinary symmetry provides both new L orientations, eligibility
provides forward auxiliary E=true and reverse E=false, and all remaining
socle/diagonal entries come from the same A. The checked full-type lemma
then yields the claimed complete next-type equality.

The existing full-closure structural theorem and literal TOP-seed
representation/no-seed theorem can now transport this result to no-I1 and
no-I2 at a **positive** tested cut, under their original hypotheses. That
last transport is a composition of published theorems, not an inference
from selected tuples alone. Full boringness still requires chosen B3.

## Audit of the stated resolved-Q construction

This section is an English argument about the construction currently in
`kk.tex`, subsection "A resolved ordinary graph containing the prescribed
Henson graph", at manuscript PR132 head
`8fe245e6a61da868557c2bb3a23d10fe7cdaa3bc`. It is not a claim that a Lean
constructor or the descending stage invariant has already been written.

Fix an independent selected set A and a non-dummy base b whose event is
omitted by its proposed Plan. Consider all uncoded selected terminals
j>b, not only those currently in a marked B3 tuple. They have complete old
passing columns, and the maintained global classes are exactly the
nonempty classes determined by those columns.

### No selected old-profile split at an omitted base

* A cover block is joined to unions of the global classes present before
  the block. Equal old profiles at a particular member imply equal profiles
  before the block, so their new bits agree. Extra previous members and
  inserted dummies only refine or preserve old information.
* For a singleton split marker, different new bits inside one old selected
  class mean both children contain selected terminals. Such a marker is a
  selected split and is retained. Therefore an omitted split marker cannot
  produce that pair. If only one child is occupied, all selected terminals
  in that old class have the same new bit.
* Before a nonselected coding base is inserted, its adjacency refinement
  has already separated each class with two nonempty children. Thus each
  resulting old class has a constant coding adjacency bit.
* At a selected coding base, all future selected terminals have new bit
  zero by independence. This case also satisfies no-split.

The selected stages used by the physical theorem are subsets of these
future selected terminals once the genuine descending inclusion and
bounded Plan roles have been established. Restriction preserves no-split.

### Actual singleton neutrality at each omitted base

The exact ordinary labelled age before and after an event is computed
from **all** old Q originals by finite common-neighbour clique capacities.
For any future selected terminal j, its canonical singleton agrees with
this same one-sort sigma: the raw singleton is independent of how other
sorts are enumerated, and canonicalization preserves it.

An omitted auxiliary block has equality as its selected age effect by the
retention rule. During the insertion of this block the selected old column
continues to label the same future terminal j. Enlarging the old prefix
can only enlarge its positive old pool and its clique capacity, so sigma
can only decrease. Equality before and after the whole block therefore
forces equality at every intermediate member. Inserted isolated dummies
leave the positive pool unchanged. This handles two-member blocks as well
as singleton split markers visible only by an equality effect.

At a nonselected coding event, the controlled pre-age identity says exactly
that the entire selected survivor age is preserved. Since j remains a
survivor, its actual singleton sigma is unchanged. At a selected coding
base or a dummy base the new bit to future selected j is zero, so its
positive pool is literally unchanged and sigma is unchanged.

These statements are ordinary finite consequences of the construction's
actual old-reference age invariant and event effects. They do not derive
singleton neutrality from arbitrary assigned canonical labels, nor from a
numerical-H selected shadow. Establishing that the infinite construction
maintains this exact invariant is a separate formalization task.

## Concrete nonvacuity and independent necessity checks

The new premises coexist with a positive eligible stage. Take k=2, N=35,
so `p(i,m)=6*i+2*m`. Put coded(false) at bases 1 and 2, coded(true) at
bases 3 and 4, and dummy everywhere else. Let the base edges be exactly
{1,3}, {1,4}, {2,3}, {2,4}, symmetrically. Choose the dummy cap at
`p(5,2)=34`, U={34}, and J=Plan={22,28}. The stage originals are exactly
{22,28,34}. At the tested cut `p(2,0)=12`, their literal free levels are
17,23,29, so every original is eligible. Both selected TOPs have the same
complete old type at 12 and new bit true. Their old generation-zero bit at
`p(1,0)=6` is true, while the cap's is false.

For each selected future base, the old positive pool before base 2 is
{1} and afterward is {1,2}. These pools have the same clique capacity 1,
since bases 1 and 2 are nonadjacent. Thus each exact singleton sigma is 2
before and after, and selected no-split holds. The Q graph is bipartite,
hence K4-free; all role and block-interval axioms hold. This is a genuine
finite physical-stage instance, not a claimed exact AlgorithmRun stage.

Remove only edge {2,4} from this example. Both selected singleton sigmas
remain 2 before and after base 2, but their old profiles still agree and
their new bits now differ. Thus actual singleton neutrality alone does
not imply selected no-split or whole-stage coherence. Conversely, the
published 23 November cap example has selected no-split but lacks singleton
neutrality: its positive TOP singleton drops from 3 to 2 at the tested
base. Neither of the two new construction properties can be discarded.

## Adversarial checks and limits

1. The old witness is derived from explicit exact canonical capacity
   equality and positivity; it is not an unexplained hypothesis.
2. All old Q bases are used in sigma, including omitted earlier events.
3. Equality across a two-member omitted block gives equality at every
   member by monotonicity; whole-event equality is not substituted blindly.
4. Selected no-split alone is insufficient; the published cap example
   violates singleton neutrality and is correctly excluded here.
5. Singleton neutrality alone is insufficient; selected no-split remains
   a separate consequence of actual class refinement and retention.
6. Every source comparison includes genuine eligibility at cut+1.
7. The second source is decoded from its forced positive **old** bit,
   so no unsupported coverage of fake or zero-generation names is assumed.
8. The selected same-base TOP case is excluded by its actual free cut,
   not by address order alone.
9. Auxiliary same-base retention contradicts the omitted-base predicate;
   later retained auxiliaries use block convexity only modulo dummies.
10. A dummy tested base must use the separate zero-column argument;
    old auxiliary columns need not vanish across a dummy inside a block.
11. The theorem concerns complete physical L+/E types, with all negative
    old atoms retained. No auxiliary E is manufactured on ordinary witnesses.
12. The proposed Q exists only in English in this development; a Lean
    constructor, actual stage inclusion, chosen B3, odd-cut closure, and the
    common labelled source remain outside this new implication.
