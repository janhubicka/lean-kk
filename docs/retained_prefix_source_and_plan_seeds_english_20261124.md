# Retained prefix sources and exact planned levels

24 November 2026. English mathematical proof and application audit before
any new Lean implementation.

Baseline: `lean-kk` commit `ddb01a336e60d51ce0db289f0c3ab327a14635d8`;
successor framework pin `a74c10761303a18649053f2af3a1a1697f032e13`.
Manuscript audited: PR 132 head
`8fe245e6a61da868557c2bb3a23d10fe7cdaa3bc`, the olive subsection
`app:independent-small-upper`.

## 1. What this audit establishes

There are two different tasks in the proposed upper-bound proof.

1. Construct an actual monoid map whose represented levels through the
   cap are exactly the finite prescribed set, and whose whole-node range
   contains the cap and each selected prefix seed.
2. Identify the selected inverse prefix codes of any such map from the
   complete retained ordinary and auxiliary tables.

The second task does **not** require equality of every compressed Kpt
parameter node across occurrences. Full parameter-closed source control
is essential when proving the omitted cuts boring, but the final Ramsey
transfer only requires one common selected G+ prefix-chain source.
`PrefixChainOrbitTransfer.prefix_chain_orbits_colour_factors` is the
already checked transfer with precisely this conclusion as an input.

The published successor framework already proves exact four-table
recovery: `shapeMap_recovers_ordinaryCode` in
`GPlusRetainedCodeRecovery.lean`, and `shapeImageRetainedCode_eq` in
`GPlusCanonicalCodeReconstruction.lean`. These recover both Boolean
values of all binary, unary, diagonal and auxiliary E atoms. They are
stronger than equality of ages or cut-star spectra.

The argument below establishes the generic exact-plan reduction and
the ordinary-code identification in English. It does **not** establish
the outstanding off-plan boringness premises for the actual resolved Q.

## 2. Force precisely the planned seed levels using an ordinary run

Work in an SM-tree with the usual actual meet/parameter closure. Let U
be a node of level tau, and let I be a finite set of natural numbers
such that tau belongs to I and every member of I is at most tau. Set

    X_I = { ancestor(U,i) : i in I }.

The ancestor uses the stated bound i <= tau. In particular U itself is
an initial seed. If 0 belongs to I, its ancestor is also an initial seed.
No ancestor at an unplanned level is inserted.

Choose the actual `canonicalAlgorithmRun H X_I tau`; its existence is
already proved for every seed set and height. Write R for this run.

### Planned levels are selected

If i in I and i < tau, the actual node ancestor(U,i) belongs to X_I,
hence to the closure at the actual pre-cut stage R.I(i+1). Its level is
i. It witnesses I1, so the interesting branch inserts i into R.I(i).
The final-tail identity then gives i in R.I(0). The level tau belongs
to R.I(tau) by `topI`, and hence to R.I(0) by the same tail identity.
Thus I is contained in R.I(0), without using E1 or a boringness premise.

### Descending off-plan exclusion gives the reverse containment

Suppose one proves the following local implication for this enlarged
seed family, at each actual tested cut c < tau:

    c not in I and R.I(c+1) subset I
      imply not IsInterestingAt(H, closure(R.I(c+1),X_I),c).

This is a genuine local construction obligation; it is not assumed to
follow from equality of selected ages. Descending induction gives
R.I(c) subset I at every c <= tau. The top case is R.I(tau)={tau}.
If c belongs to I, either algorithm branch preserves containment. If
c does not belong to I, the displayed implication selects the
noninteresting branch, so R.I(c)=R.I(c+1). Therefore R.I(0) subset I.

Combining the two directions gives the **literal equality** R.I(0)=I.
The final-tail theorem strengthens this to

    R.I(c) = { i in I : c <= i }

for every c <= tau. In particular the induction uses the actual
pre-cut stage, not a guessed final pool.

### Whole-node coverage and the exact level map

All X_I nodes have level at most tau. Under the framework's actual E1,
`R.fullInvariant` supplies the whole-node range coverage of X_I for
F=R.F(0). `stageFullInvariant_levelRange` gives exactly

    F.map.levelRange = I union { q : tau < q }.

This is a theorem about an ordinary AlgorithmRun. No new optional
retaining branch is inserted into the definition of that run.

### Compatibility with the physical root pool

When U is the genuine finite numerical-H cap original, every member
of X_I is below that same original. Consequently X_I is represented by
the singleton physical original pool {cap}. Adding these particular
seeds does not introduce a second physical root original. At every
c outside I there is no initial seed ending at c, by the exact ancestor
level equation.

The existing generic stage-coherence structural theorem and generic
original-pool theorems can therefore be applied to X_I. The previous
corollaries specifically quantified over `numericHTopGenerationSeeds`
must not be reused unchanged: X_I is a different seed family. This is
precisely why the general seed-representation and no-seed hypotheses
were retained in the generic modules.

## 3. Retained-coordinate chunks are determined by the record

For the manuscript's k=4 construction, p(b,r)=10b+2r. Every meaningful
base b has an isolated dummy immediately before it, and b>0. The exact
first missing E coordinates are

    f(b,1)=10(b-1)+1,
    f(b,2)=10(b-1)+3,
    f(b,3)=10(b-1)+5,
    f(b,4)=10(b-1)+9.

The top formula differs from the non-top formula: the last free cut
is +9, not +7. These are the exact generated-E formulas, not a choice
of convenient free cuts.

For every retained auxiliary member b, its ordered chunk consists of
the four free cuts f(b,1),...,f(b,4), followed by its five coordinates
p(b,0),...,p(b,4). This contributes nine coordinates. For a selected
coding base b, the chunk consists only of f(b,4), p(b,4), contributing
two coordinates. The initial anchor contributes coordinate 0. The cap
end tau is a represented **end level**, and is not an additional
ordinary coordinate in the compressed cap code.

These chunks are disjoint and occur in the same order as their
meaningful bases. Indeed, a previous meaningful base a satisfies
a <= b-2, so p(a,4) < f(b,1). All f(b,r) are odd, all p(b,r) are even,
and f(b,4) < p(b,0). The initial dummy makes 0 < f(b,1) for the first
possible meaningful base. Omitting any number of other meaningful
bases changes physical distances but not this chunk order.

Hence, if B(R) is the total number of members in retained auxiliary
blocks, the number of ordinary coordinates in the common retained
code is

    N(R) = 1 + 9 B(R) + 2 n.

The full planned level set has N(R)+1 members, including the final end
level tau. This count concerns the proposed record construction; it
does not identify the actual run until Section 2's off-plan implication
has been established.

### All retained ordinary atoms

The record determines each retained block's one- or two-member size,
its selected neighborhood, and the ordered ancestry of every selected
terminal at that event. Distinct auxiliary blocks are nonadjacent.
The two members of a retained two-member block have their internal
base edge. A block has no edge to already coded terminals. Selected
terminals are pairwise nonadjacent. Thus every base pair among retained
meaningful bases is decided by the record, including nonedges.

The fixed gate s<r or s=r=4 determines all copied ordinary edges. Odd
free-cut coordinates and the initial dummy anchor have no ordinary
edges. The diagonal is false and there is no unary relation in this
graph signature. A split marker visible only as the singleton cover
3->2 has the same one-member physical retained chunk and selected
neighborhood as that singleton-cover block; its discarded global role
need not be an extra record bit.

### All retained E atoms

An odd target or generation-zero target has an empty incoming E
column. A positive-generation target p(b,r) has the strict initial
segment of retained coordinates preceding its marked free cut f(b,r).
That free cut is retained and lies earlier than the target. Therefore
the retained E matrix is determined solely by the ordered chunks and
their generation/free-cut tags. This includes all absent E atoms and
the reverse directions; E is not symmetrized.

Keeping the first missing E coordinate also preserves spacing after
compression: every positive E pair has that coordinate strictly
between its endpoints. For an ordinary edge whose later base is b and
generation is r, r>0 and every earlier meaningful-base coordinate lies
below f(b,r), so the required E incidence is retained.

## 4. Exact inverse prefix-code identification

Suppose Section 2 has produced an actual monoid map F covering U and
all X_I seeds, with represented levels through tau exactly I. Let U*
be the unique source node with F(U*)=U and write N=lev(U*). The strictly
increasing level map lambda sends N to tau. Its first N+1 values are
exactly the increasing enumeration

    r_0 < ... < r_N=tau

of I. Thus N+1=|I|. The final endpoint r_N is not an ordinary coordinate
of U*, whose ordinary code has size N.

For the present application n>=1, a selected coding position lies
strictly below tau, so N>0. A generic plan consisting only of its top
endpoint need not have a positive source code; the run lemma remains
valid in that boundary case but makes no positive G+ vertex assertion.

`shapeMap_recovers_ordinaryCode` says literally that

    ordinaryCode(U*)
      = ordinaryCode(U) reindexed by j |-> r_j, for j<N.

All four finite tables are included. Since U is an actual numerical-H
original, its ordinary socle is the physical initial code below tau.
The right side is therefore exactly the complete record-determined
matrix from Section 3. This deduction does not assume equal full raw
cap types or equal Kpt parameter lists across different occurrences.

For a selected position d=r_j with j<N, the actual seed U restricted
to d is in F's range. Preservation and reflection of the ancestor
order identify its unique preimage as U* restricted to j. The genuine
strict representing pair (U* restricted to j,U*) consequently maps
to (U restricted to d,U). Its source vertex is the initial prefix of
ordinaryCode(U*) of size j+1. Thus the source for each selected label
is determined by the fixed retained code and that label's chunk rank.
The selected prefix sizes are **j+1**, not j. They strictly increase
in coding order, giving injectivity without a separate label choice.

For two occurrences of the same record, Section 3 gives the same
complete retained code and the same selected chunk ranks. Prefix
uniqueness identifies all selected inverse vertices label by label.
Their actual monoid maps provide the common source orbit. Equivalently,
one may use `shapeImageRetainedCode_eq` directly on each lifted G+
vertex and compare the two physical compressed prefix tables.

For records with no occurrence, the colouring transfer can omit them
from its finite index set. Alternatively the manuscript's explicit
finite carrier construction supplies validity: a retained base clique
uses one auxiliary block and at most one independent terminal, has
size at most three, and numerical generation copying cannot create a
larger clique; the retained E columns are downward, spaced and linked.
One then adds the checked neutral gap/cap carrier. No source existence
argument should select an occurrence without treating empty fibres.

## 5. Adversarial scope checks

1. X_I contains only the planned ancestors, not every ancestor below U.
   Full prefix saturation would force all physical levels and defeat
   compression; `PrefixSaturationI1Obstruction` remains applicable.
2. The enlarged seeds change the actual run. Off-plan boringness must
   be proved for this enlarged family, not borrowed from a smaller run.
3. The physical root pool stays {cap}; this does not say the full
   meet/parameter closure has only one original or only those seeds.
4. Every off-plan structural application uses its actual closure and
   the full current stage, including generated parameters and meets.
5. Exact selected-level equality is derived by descending induction;
   no final-pool inclusion is assumed before the induction.
6. Whole-node E1 coverage is retained. Matching crossing tables alone
   does not produce preimages of terminals or cap nodes.
7. The level map is strictly increasing and enumerates I only through
   the cap. Its full infinite range also contains every level >tau.
8. The cap end is not an extra ordinary coordinate. The source code
   has |I|-1 coordinates, and a selected source rank j gives size j+1.
9. Odd coordinates have empty incoming E but can have outgoing E.
   They are only ordinary-L isolated, not isolated in L+.
10. The top free-cut formula has offset 9 rather than 7 at height four.
11. Distinct retained chunks cannot collide because an actual dummy
    lies before every meaningful base; this premise cannot be dropped.
12. The complete retained E matrix is compared, not just its positive
    incidences against selected terminals.
13. The source is not claimed to be a minimal envelope of the selected
    vertices. It is an envelope of the larger planned-prefix seed set.
14. G+ prefix codes retain the complete ordinary socle L+/E structure;
    they do not determine a raw Kpt distinguished-type-vertex column.
    The argument never uses the false converse.
15. The common-source conclusion follows after full off-plan boringness
    and record-realization checks. It does not independently establish
    the characterisation or the numerical upper degree.

## 6. Suggested narrow formal continuation

The generic run lemma should derive exact I and output level range from
planned-level seed witnesses and the actual local off-plan implication.
It should not take final-level equality as a premise. A physical
ancestor-seed adapter should discharge the root-pool, boundedness and
off-plan no-seed facts for one actual cap original.

The common-source bridge should compare physical finite-code reindexings
along explicit level-map coordinates and use the published exact
recovery theorem. It should not assume equality of inverse-image sets,
source tops, or selected source values under a new name. Formalizing the
finite record's chunk/table construction is a separate concrete task;
the English verification above does not turn an arbitrary payload type
called a record into that construction.
