# Chosen marked B3 from actual selected-TOP reference-age neutrality

Date: 2026-11-24. Status: proposed English proof for independent review;
not yet a kernel theorem or a completed resolved-Q construction.

## Exact statement

Let Q be a simple K4-free graph on natural-number bases, and let H be
its finite numerical height-k expansion, with k >= 3. Fix a cut
c = p(b,g) below the finite carrier bound, where 0 <= g < k. Fix a finite
list of selected TOP originals p(j_t,k), indexed by t in a finite sort
set D, with every j_t > b. Repetitions of j_t are permitted. Put
P0 = {q : q < b}, P1 = {q : q <= b}, and a(q,t) = E_Q(q,j_t).

The reference ages F0,F1 are the **actual** integer-witness canonical
ages of these columns over the induced old Q graphs P0,P1:

    Fi = integerGraphAgeCanonical D 4
           (finiteOldColumnRawBound E_Q 4 D Pi a).

Assume F0 = F1 on every nonempty admissible support. This is equality
of the full labelled finite continuation ages, not equality of singleton
ranks and not equality of raw bounds. Suppose every genuinely chosen
upper ordinary-L type of a selected-stage prescribed function is the
complete (c+1)-type of one of the displayed TOP originals. Then that
prescribed function passes corrected B3 for the Henson forbidden family.
In particular the statement applies to the marked selected-TOP source
once its exact chosen-output coverage and the displayed actual age
identity have been instantiated.

No no-I1/no-I2 premise is needed for this marked-only assertion.
The existing no-I2/representation transfer is still needed when passing
from marked B3 to the full actual source.

## Numerical age sandwich

Write H_<c and H_<=c for the entire initial numerical coordinate pools,
including odd coordinates and every generation. Give each sort its
actual complete TOP ordinary column. For every nonempty support T:

1. All generations of every Q base q<b lie in H_<c. Every one of their
   bits to p(j_t,k) is E_Q(q,j_t): the lower-generation gate is open,
   and the TOP-to-TOP clause handles generation k. Thus the old complete
   block common-neighbour capacity is exactly the old Q capacity.
   This is the content of FullRealGenerationCapacity after identifying
   its pulled-back columns with the actual physical TOP columns.
2. Every numerical common neighbour of T in H_<=c is a real coordinate:
   odd/fake coordinates have zero bits, and T is nonempty. Its decoded
   base is <=b. A numerical clique projects injectively to a Q clique,
   with all directed edges preserved, and every projected vertex is a
   common Q neighbour of T. Therefore its capacity is at most the
   common-neighbour capacity over P1.
3. Inclusion of the complete old blocks in H_<c and H_<c in H_<=c gives
   the intermediate inequalities. Reversing these inequalities in the
   raw allowance 3-capacity and applying monotonicity of the canonicalizer
   yields

       F1 <= F(H_<=c) <= F(H_<c) <= F0.

The assumed equality F0=F1 makes both complete physical prefix ages
equal to this same age. Repeated copies of one base do not increase a
clique: there is no ordinary edge between two copies of one base.
No equality of raw and canonical bounds is used.

## Exact corrected-B3 argument

Suppose the genuine marked prescribed data failed corrected B3.
The already checked Henson failure theorem supplies a bounded ordinary
continuation W with the **same entire initial L socle through c**,
all future complete L types among the actual chosen outputs, and no
forbidden pattern after deleting c. Loops and asymmetric pairs have
already been excluded by that theorem; a K4 is the remaining obstruction.

Choose for each future vertex a sort whose displayed TOP type is its
complete L type. Different future vertices may receive the same sort.
This choice preserves every old/future bit in both directions, including
zeros, because it is equality of complete L types. The continuation's
future-future graph is unchanged and may have arbitrary allowed edges.

Apply finiteOldFuture_free_iff_canonical_support to the entire finite
future graph and old prefix H_<c. Deletion of c is K4-free, so every
future clique satisfies every canonical support constraint. The numerical
age sandwich makes these exactly the constraints for H_<=c. The same
reference-age theorem, in the reverse direction, shows that adjoining
c is K4-free. This contradicts the extracted K4.

The proof works for an empty chosen source as well: a failed B3 witness
would need a future vertex with a prescribed upper type, which is
impossible. Alternatively the existing empty-source theorem applies.
No auxiliary E values are imposed on the arbitrary age-test continuation.
E is used only to obtain the genuine chosen physical type and eligibility.

## Application to resolved Q: what must be checked

Use D consisting of the actual eligible selected TOP names (or a finite
list covering their complete types). Their bases are strictly later than
b: positive free levels of a TOP at base j lie before p(j,0), so eligibility
at p(b,g)+1 excludes j<=b. Chosen marked outputs are complete types of
eligible marked originals by selectedStagePoolPrescribedData's definition.

For an omitted auxiliary block, equality of the selected canonical age
before and after the whole block, together with monotonicity under old
prefix extension, gives equality at each constituent base, including
interleaved isolated dummies. The labels must refer to the same remaining
selected terminals throughout; pulling back class labels permits repeats.
For an omitted nonselected coding event, the controlled pre-age formula
gives equality on the survivor sorts. For selected coding bases, the
independence/chronological-role theorem gives an empty positive cut-star;
the existing empty-star B3 theorem applies directly. Isolated dummy bases
also use that theorem. The retained auxiliary bases have no omitted
generation in the plan.

These event facts are asserted by the ordinary construction and require
an explicit finite-prefix realization in the final formal application.
The age sandwich and B3 reduction must not be recorded as though that
realization or the descending stage inclusion were already formalised.

## Adversarial checks required

- Genuine full canonical age equality on all supports, not singleton ranks.
- Actual old Q prefix and actual selected TOP columns, not stipulated ages.
- All complete old numerical blocks present, including their TOP copies.
- All chosen outputs covered; eligibility excludes bases <=b.
- Both old/future edge directions and all negative bits fixed.
- Arbitrarily many repeated labels in a future clique and arbitrary future edges.
- Generation zero, positive lower generations, a two-member omitted block,
  empty source, and odd dummy gaps.
- No E structure fabricated on the arbitrary ordinary continuation.
- No circular use of no-I2 or full-source B3 to establish marked B3.

### Why singleton neutrality alone cannot replace the full age premise

Take two selected independent future bases x,y. In the old Q prefix put
nonadjacent bases a,a' with columns (1,0),(0,1) to (x,y). A new base b
has column (1,1), and all three old bases are mutually nonadjacent.
The before and after singleton capacities are both (2,2). Before b the
mixed support has canonical capacity 3: the clique vector (2,1) is
feasible. After b the mixed capacity is 2. Thus singleton neutrality and
selected no-split may both hold although the full age changes.

An arbitrary future triangle with two vertices labelled x and one
labelled y is compatible with the old prefix. Restoring b forms K4.
At the generation-zero numerical cut, all copies of earlier bases are
old, the selected TOP columns are exact, and the same triangle witnesses
failure of marked B3. Inserting isolated dummy bases preserves this
example. The resolved construction would retain this strict mixed-support
cover; treating it as omitted would be a genuine error.
