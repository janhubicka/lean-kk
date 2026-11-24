# Completing the ordinary resolved-Q application and selected source orbit

24 November 2026. Proposed replacement English for independent review before
editing the manuscript. This note does not modify `kk.candidate.tex`.

## Audit conclusion and intended placement

The explicit construction in Lemma `small-independent-resolved-Q` already
supplies the ordinary invariants required by the exact finite Plan theorem.
The missing link is their event-by-event application to fixed selected
terminal columns. No new infinite construction, density hypothesis, or
selected-age-to-full-source axiom is needed. The following text makes that
link explicit. Keep the global Lean validation markers pending until the
constructor, record parser and final theorem composition are formalized.

The first proposed insertion belongs at the end of the resolved-Q proof,
after the selected record has been defined. It can alternatively appear
immediately before the full-pool boringness lemma. The second replaces that
lemma's remaining-obligations paragraph after its complete cut case split.
The third completes the inverse-source proof after exact recovery of the
retained full code. It permits simplifying the alternative explicit finite
carrier construction, although that construction is mathematically sound.

## 1. Ordinary selected-column invariants: proposed manuscript text

```tex
We record the actual-column invariant needed below. At every finite
construction stage, the nonempty classes of uncoded vertices have
constant complete ordinary columns on the entire old $Q$ prefix,
and two different classes have different such columns. Initially
there is one class. A split marker gives its children different new
bits; a clique block adds a constant bit on each class; and coding
removes the singleton coded class. Before coding, the refinements by
adjacency to that vertex have made its new bit constant on every
surviving class. These operations preserve the invariant.
The class age throughout is the class of all finite $K_4$-free
gluings over that old prefix. It is not asserted to equal the age
realized inside the particular remaining subsets of $V$.

Fix the selected independent set $A$, and, at a base $b$, enumerate
its future selected bases $T_b=\{j\in A:b<j\}$ by a finite list
$(j_t:t<d)$. Use the same terminal labels on both sides of the base.
Their actual old columns are $q\mapsto E_Q(q,j_t)$. At either
endpoint, the class-column invariant identifies these columns with
the columns of their active classes. Thus the canonical pullback
identity, with that endpoint's actual class map, identifies their
full reference age with the pullback of the selected class age.
Different terminal labels may belong to the same class; the
pullback sums clique multiplicities along the class fibres.

Consider an auxiliary block which is not retained for $A$. If it is
a cover block, its restriction to the selected front is equality:
a strict restriction would have made the whole block retained.
If it is a split marker, it cannot have two occupied selected
children. With only the negative child occupied the selected age
is unchanged. With only the positive child occupied, the split
formula gives equality or the singleton cover $3\to2$; the latter
case would again have made the marker retained. A marker on a
class with no selected terminal has no selected effect. Hence the
actual full reference ages on the fixed terminal list agree at
the two endpoints of every omitted block. No coding occurs inside
a block. Extending the old prefix can only decrease each canonical
capacity, so the equal endpoint values force equality at every
individual member of the block. Inserted dummy bases change no
column and do not affect this argument.

At a nonselected coding base $b$, the current global pre-age is
$F^\ast$. If $R$ is its survivor restriction and $X$ is the set of
surviving classes adjacent to the coded vertex, actual cliques
containing that vertex give exactly the controlled pre-age formula.
Consequently its coding preserves the actual complete survivor
age. Pulling back along the before and after survivor-class maps
proves equality on the fixed list $T_b$. At a selected coding base,
all bits into $T_b$ are zero by independence, so adding that base
also leaves their age unchanged. Dummies are isolated. We have
therefore proved, at every base whose real coordinates may be
omitted, the equality of the actual full canonical ages on all
future selected columns whenever that equality is needed below.
In particular it holds at every unretained auxiliary member and
every nonselected coding base, on every nonempty support.

The selected no-split assertion concerns the same complete columns.
Suppose $j,j'>b$ are selected and their bits agree at every $q<b$.
Before a cover block they therefore belong to the same active class,
so every member of that block gives them the same bit. This also
applies at an intermediate member: equality on the longer prefix
implies equality on the prefix before the block. At a split marker,
different new bits would put selected terminals in both children,
so that marker would be retained. Before a nonselected coding,
the adjacency refinements make its bit constant on each active
class, and different classes already have different old columns.
At a selected code or dummy all relevant bits are zero. Thus every
omitted base has the required selected no-split property.

These assertions use the literal columns over all old bases.
They concern every future member of $A$, so they remain valid
on any list covering the actual positive eligible stage names,
with repeated labels or omitted classes. If there are no future
selected bases, the reference-age equality and no-split statement
have their empty-domain meanings.
```

### Why this is a proof of the required invariant

The two places where an unstated selected-shadow assertion might otherwise
enter have been made explicit. First, class ages mean exact finite gluing
ages computed from complete old columns, whereas F-star is only an actual
clique-capacity bound used to choose safe auxiliary blocks. Second, before
and after class indices are related through the actual fixed terminal list,
not identified as raw global indices. The existing arbitrary sort-map
pullback then applies, including repeated labels.

The no-split check does not claim that all global splits are retained. It
uses exactly the fact that a split with both selected children occupied is
retained. All old Q coordinates remain available when comparing columns,
including global markers omitted from the compressed selected record.

## 2. Finite restriction and complete descending application

The following paragraph is suitable immediately after the cap is chosen.

```tex
Let $b_\ast$ be the last selected coding base and let $b_{\mathrm{cap}}$
be the first dummy after it. Then $b_{\mathrm{cap}}=b_\ast+1$ and
$\tau=p(b_\ast,4)+1$. Work, for this finite argument, in the actual
numerical prefix with carrier bound $N=p(b_{\mathrm{cap}},4)+1$.
Its ordinary columns and auxiliary free cuts agree with those of
$H(Q)$ on all coordinates used here. Every selected TOP lies
strictly below $\tau<N$, and every retained auxiliary member
precedes the last selected coding. Hence the concrete $I$ is
exactly the finite retained Plan: the anchor, cap end, retained
real coordinates and their actual free cuts. The role of a coding
base records membership in $A$, and the flag of an auxiliary
member records retention of its whole block.
```

The following replaces the current conclusion that ordinary data still
have to be supplied, after the already printed odd/real case proofs.

```tex
The chronological role axioms now follow directly from the
construction: dummies are isolated, a newly inserted auxiliary
block has no edge to an earlier coded vertex or a different
auxiliary block, and retention is constant on a whole block.
Blocks are intervals modulo the inserted dummies. The selected
codes are independent. The preceding actual-column argument
supplies full reference-age neutrality and selected no-split at
every unretained meaningful base before the cap. Its finite target
list consists of all future selected bases, whose TOP coordinates
lie below $N$. Singleton neutrality follows either by evaluating
the one-sort pullback or by restricting this full identity.

We can therefore apply the preceding cut arguments to the genuine
run from $X_I$. There is no assumed equality with the final pool.
At each descending step use only
$\mathrm{Run}.I(c+1)\subseteq I$. Odd cuts use actual free-cut
closure of $I$. Omitted TOP cuts use complete stage coherence and
the nonstructural selected-cut classifier. Dummy lower cuts and
lower copies of selected coding bases have zero eligible stars.
At every remaining lower real cut, generation-zero or positive-
generation coherence excludes (I1) and (I2), and full reference-age
neutrality proves the genuinely chosen full (B3) test by its exact
cut-star core. Transfer between stage and final names concerns
this same closure and uses the no-(I2) already proved; it assumes
no equality of their name sets.

These cases exhaust the positive coordinates below $\tau$; zero
belongs to $I$. Thus every off-plan step is noninteresting under
the descending hypothesis. The induction begins at the initialized
cap end and proves that no level outside $I$ is selected. Every
level of $I$ below $\tau$ is selected because its literal ancestor
seed is an (I1) witness, and $\tau$ is selected by initialization.
This proves the full-pool boringness lemma for the enlarged seed
family and the exact identities for $\mathrm{Run}.I$ used below.
The remaining Lean work is the construction and event-invariant
instantiation of these ordinary data and the final theorem
composition; no further local cut case is assumed in this argument.
```

No new positivity assumption is being hidden: the manuscript has
1 <= n <= 3, so the last selected base and positive cap end exist. The
more general finite Plan theorem also handles a zero cap end separately.

## 3. Common selected source after exact Plan and literal table recovery

Once the level range and complete retained table are proved, no equality
of all parameter-node records across occurrences is necessary. The actual
remaining reasoning is as follows; it can replace the conditional closing
paragraph of the common-source proof.

```tex
For each occurrence, the actual envelope map has the proved level
range. Its increasing level map therefore enumerates $I$ through
$\tau$. If $U^\ast$ is the whole-node preimage of the cap, then
$\operatorname{lev}(U^\ast)=|I|-1=N(R)$, and the source position
corresponding to each selected code is its rank in that enumeration.
Ancestor preservation identifies its representing pair with the
corresponding prefix pair of $U^\ast$. The induced action on $G^+$
preserves and reflects every ordinary and auxiliary atom, so the
entire source code on coordinates below $N(R)$ is exactly the
order-compressed retained table.

That table and the marked coordinate ranks depend only on $R$:
its auxiliary member chunks have nine coordinates, its selected
coding chunks have two, and its anchor has one. Distinct blocks,
already coded terminals, fake coordinates and same-base pairs
have the specified zero ordinary bits; the generation gate gives
all remaining ordinary bits. The retained first missing-$E$
coordinates determine both directions and all negative auxiliary
bits. The cap end is an end level, not an extra ordinary coordinate.
Thus every occurrence gives the same genuine selected $G^+$
prefix-code tuple, with labels in coding order.

For a record which occurs, choose one finite full carrier
representing that common tuple. For each occurrence, restrict its
actual global envelope map to this fixed carrier. The induced
$G^+$ action on the common tuple is the selected occurrence,
because it is well defined independently of representing pairs.
The fixed carrier need not use that occurrence's particular
inverse cap or parameter-name enumeration. Consequently every
occurrence is in one actual monoid orbit of the fixed selected
source. Records with no occurrence may be omitted, leaving at
most $|\mathcal R_n|$ sources for the finite Ramsey iteration.
```

This uses a finite carrier of genuine prefix-code points, supplied by the
already checked prefix-chain carrier theorem or by the explicit neutral-cap
construction in the current proof. The latter construction is optional.
The remaining formal work is a literal record-to-chunk table theorem and
its composition with exact level-map recovery and the induced action. It
is not an additional mathematical common-orbit hypothesis once those
identifications have been proved.

## 4. Status language after independent acceptance

If these completions are inserted and accepted, the introductory claim of
a completed ordinary proof for the small independent cases can remain,
while the global Lean marker stays pending. The upper subsection should
then describe its finite construction proofs as established mathematics
with outstanding formalization, rather than saying that its conclusion
assumes unproved full-source and common-source assertions.

The separate general successor-diary framework remains conditional for
arbitrary finite graphs. The argument here uses selected independence in
both the zero-star/code steps and the retained-source graph and does not
promote that general characterization.
