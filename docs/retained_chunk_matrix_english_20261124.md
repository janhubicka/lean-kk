# Concrete retained chunk matrices

24 November 2026. English proof before any further Lean implementation.

This note isolates the finite calculation behind the remaining table
premise of `Kk/RetainedPrefixSource.lean`. It strengthens the earlier
retained-prefix audit by giving a literal atomic matrix determined by
ordered retained base data. It does not assume equality of compressed
tables, and it does not claim to have implemented the parser from a
manuscript record to that base data.

## 1. Common combinatorial data and two physical realizations

Fix a positive numerical height `k`. Take an ordered finite list of
retained meaningful base members, indexed by `i < B`. A member is
either auxiliary or a selected coded terminal. The common data comprise
these flags and a directed Boolean base table `D(i,j)`.

Two physical occurrences have base positions `b_F(i)` and `b_G(i)`.
For each occurrence require:

- every retained base position is positive;
- if `i < j`, then `b(i) + 2 <= b(j)`;
- the physical ordinary graph restricted to these bases is exactly
  `D`, in both directions;
- base zero is isolated in both ordinary directions, and all ordinary
  loops are false;
- every coordinate used below lies inside the actual finite numerical-H
  carrier.

The two-position separation follows in the intended construction from
the dummy immediately before every meaningful base. Intervening omitted
events may increase the separation arbitrarily. The two occurrences
need not use the same physical base numbers or the same number of
omitted events.

These are finite numerical/ordinary-graph conditions. They do not assert
equal G+ sources, equal ages, equal inverse-image sets, equal parameter
pools, or any full matrix equality.

## 2. Slots and their numerical coordinates

Use an anchor slot and, for each member `i`, free slots `f(i,r)` with
`1 <= r <= k` and real slots `p(i,r)` with `0 <= r <= k`.
An auxiliary member keeps all these slots; a coded member keeps only
`f(i,k)` and `p(i,k)`. The anchor has physical coordinate zero.

More explicitly, for the fixed flag function `kind : Fin B -> {aux,code}`,
the finite slot set is the disjoint union of

    {anchor},
    {(i,free,r) : 1 <= r <= k and (kind(i)=aux or r=k)},
    {(i,real,r) : 0 <= r <= k and (kind(i)=aux or r=k)}.

Here the two displayed copies of a pair `(i,r)` are distinct constructors,
and `i` is the event-member index, not its physical base number. The
matrices and selected labels use these same indices in both occurrences.

For a positive physical base `b`, the slot coordinates are

    p(b,r) = hPosition k b r,
    f(b,r) = hPosition k (b-1) (r-1) + 1,  if 0 < r < k,
    f(b,k) = hPosition k (b-1) k + 1.

The special TOP formula is essential. At height four the free offsets
are `1,3,5,9` inside the preceding dummy block, not `1,3,5,7`.
By the exact generated-E formulas these are the actual first missing E
coordinates of the respective positive real originals. Generation zero
has free level zero.

Order slots by placing the anchor first, then members in their common
index order, and within each member all free slots in increasing
generation followed by all real slots in increasing generation.
This abstract order agrees with the physical coordinate order in both
occurrences:

1. Every free slot is positive and odd; every real slot is even.
2. The free slots of a member strictly increase, and its last free slot
   precedes its generation-zero real slot.
3. If `a + 2 <= b`, then `p(a,k) < f(b,1)`.

The last inequality bounds the entirety of an earlier retained chunk
below the entirety of a later one. It also proves that slots from
different members cannot collide. Thus the same ordered finite slot set
has order-preserving injective physical realizations in both occurrences.
If there are `A` auxiliary members and `n` selected coded members, its
size is `1 + (2*k+1)*A + 2*n`; for `k=4` this is `1+9*A+2*n`.

## 3. Explicit ordinary table

All ordinary atoms involving a free slot are false, since free slots
are odd. Every ordinary atom involving the anchor is false, using the
isolated base-zero hypothesis; the anchor is a real generation-zero
coordinate, so its isolation must not be inferred from oddness.

It remains to compare two real slots `p(i,g)` and `p(j,h)`.

- If `i=j`, the ordinary atom is false: the crossing generator requires
  distinct base indices, and bounded address injectivity excludes an
  alternative presentation of either endpoint.
- If `i<j`, the atom is true exactly when `D(i,j)=true` and
  `(g<h or g=h=k)`.
- If `j<i`, the atom is true exactly when `D(i,j)=true` and
  `(h<g or h=g=k)`.

The third case uses the actual reversed ordered tuple in
`HNumericCrossing`. It does not replace `D(i,j)` by `D(j,i)` unless
symmetry is separately available. The two physical occurrences therefore
have identical directed Boolean ordinary tables, including all false
entries. Their unary tables are empty and their diagonal tables are
false by the graph-loop hypothesis and the exact singleton constructor.

## 4. Explicit auxiliary E table

The incoming E column of the anchor, a free slot, or a real
generation-zero slot is empty. These statements follow respectively
from the initial-base, odd-target, and generation-zero generated-E
formulas. Odd slots may have outgoing E and must not be deleted from
the source calculation.

In particular, this is a statement about the actual generation-zero
free level, not a convention: for `k>0` and any base `b`,
`generatedE k b 0 u` is impossible. Its strict gate would require a
natural generation below zero, and its TOP tie would force `k=0`.
Bounded address injectivity then makes the exact E column at `p(b,0)`
empty. Finite target restriction preserves that emptiness. The defining
equivalence `E(u,v)=true iff u<freeLevel(v)` implies
`freeLevel(p(b,0))=0`, by testing `u=0` if the free level were positive.
This applies equally to the anchor `p(0,0)`.

Let the target be a positive real slot `p(j,g)`, with `1 <= g <= k`.
Its exact incoming E column is the strict initial segment below
`f(j,g)`. The slot order just proved gives the following complete rule:

- the anchor has E to the target;
- every slot from a member `i<j` has E to the target;
- a free slot `f(j,r)` of the same member has E to the target exactly
  when `r<g`;
- all real slots of the same member and all slots of later members
  have no E to the target.

This rule uses the physical numerical E relation, which depends on the
generation scheme and not on which ordinary base edges happen to be
present. The TOP free-cut exception still yields the same comparison
`r<g` among free-slot tags. At `r=g`, the free slot is the first missing
coordinate, so its E bit is false. This is a strict inequality.

Because all slot coordinates lie below the finite carrier bound, the
finite constructor's target truncation introduces no additional cases.
The complete directed E table depends only on slot order and tags, hence
is the same in both occurrences.

## 5. Literal finite code equality

Enumerate the common finite slot set in its common order, obtaining
coordinate maps `rho_F : Fin M -> Fin N_F` and
`rho_G : Fin M -> Fin N_G`. Sections 3 and 4 identify all four tables of
the two pullbacks, and both pullbacks have size `M`. Extensionality gives

    (FinitePartialCode.ofEnumerated H_F).reindex M rho_F
      = (FinitePartialCode.ofEnumerated H_G).reindex M rho_G.

The same proof applies to every common initial slot segment, including
the segment ending at a selected coded TOP. Its length is that TOP's
slot rank plus one. This is a concrete way to supply the retained-target
table equality used by `RetainedPrefixSource`, once the maps `rho` have
been identified with the actual AlgorithmRun level maps.

## 6. Connection to manuscript records and remaining obligations

For the manuscript's selected histories, the common base data are
obtained by expanding each retained event to its one- or two-member
auxiliary block, and each selected code to a terminal member. The event
order gives the member order. Each record determines the retained
block size and its selected terminal neighbourhood via the ordered
class ancestry. Within a two-member block the base edge is true;
different blocks are nonadjacent; selected terminals are independent;
and a block is nonadjacent to already coded terminals. These facts
determine every entry of `D`.

A split marker whose only visible selected effect is the singleton
cover `3 -> 2` gives exactly the same one-member chunk and selected
neighbourhood as that cover. No extra discarded global-event flag is
needed in the matrix calculation.

There remain concrete application tasks after this finite calculation:

1. Extract these ordered retained members and common `D` from the actual
   resolved-Q construction and equal records.
2. Identify the explicit `numericRetainedPlan` through the cap with this
   ordered slot set plus the cap endpoint. Every retained real generation
   must actually lie strictly before the cap; a retained flag alone does
   not prove this finite bound.
3. Finish the genuine descending omitted-cut argument for the enlarged
   planned-prefix seed family, obtaining exact actual selected levels.
4. Use that exact level range and the cap/terminal range lifts to show
   that the actual level-map coordinates are these slot enumerations.

The cap end is a final represented endpoint, not an extra ordinary slot.
The last selected TOP is the last ordinary slot in the intended
construction. Neither an unproved source equality nor a mere comparison
of local capacity profiles can replace these application steps.

## 7. Roots, repeated templates, and empty boundary cases

The isolated dummy cap is generally a positive-generation original with
a positive odd free level. Its zero ordinary upper column does not give
an empty auxiliary E column or free level zero. This finite-table lemma
compares the ordinary socle below the cap; it does not replace the cap's
complete distinguished type, delete its root role, or remove it from
the actual eligible stage. Actual root representation and E1 coverage
remain supplied by the planned-prefix construction.

Repeated event shapes or repeated age values are allowed. They do not
identify slots: every retained member keeps its own ordered index `i`,
even if its flag and all visible incidence values match another member.
An auxiliary block with two members gives two such indices, separated
physically by a dummy; its internal edge is recorded in `D`. Selected
terminals retain their coding-order labels. Thus the source-order claim
uses equality of the ordered record, not equality of an unordered list
of event templates or a multiset of ages.

The finite matrix calculation also makes sense with `B=0`: there is one
anchor slot, provided its physical coordinate is inside the chosen
carrier. There need not be a selected terminal or a labelled G+ output
in that case. To identify a planned cap source with all `M` ordinary
slots, one must additionally require the cap endpoint to be strictly
after every slot, including the anchor. Then the endpoint is distinct
and the complete planned level set has `M+1` members.

If the cap end is zero, the anchor and endpoint coincide; the inverse
cap may have size zero, and neither that cardinality formula nor a
positive-size G+ cap follows. The manuscript application restricts to
`1<=n<=3` and takes its cap after the last selected TOP, so the strict
endpoint bound is present. Records with no physical occurrence must
still be omitted from the occurrence-based source index or realized by
the separate finite carrier construction; no occurrence may be chosen
from an empty fibre.
