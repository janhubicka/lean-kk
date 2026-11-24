# Omitted TOP cuts: whole-stage coherence and actual nonselection

24 November 2026. English proof before implementation of
`Kk/TopGenerationStageCoherence.lean`.

## The missing case in the current cut partition

The published positive-generation theorem only covers `0<g<k`.
An omitted TOP coordinate `p(b,k)` can belong to a nonselected coded base,
an unretained auxiliary block, or a dummy base. The fact that TOP cuts
pass corrected B3 does not exclude structural I1/I2 there. The proof below
supplies that separate structural exclusion on the whole eligible stage.
It uses the canonical bounded root/Plan roles and actual descending stage
inclusion, but no singleton neutrality, selected no-split, block convexity,
or age equality. Those stronger construction properties remain needed at
generation zero.

## 1. A later positive neighbour of a TOP is another TOP

For any ordinary base table B, suppose

    p(k,b,k) < y,  L_H(p(k,b,k),y)=true.

Here `p(k,b,g)=hPosition k b g`. Expand the exact
`HNumericCrossing` generator. Its two base indices i<j and generations
q,m are bounded by k. A forward presentation gives

    p(k,b,k)=p(k,i,q),  y=p(k,j,m),
    q<m or (q=m and m=k),  B(i,j)=true.

Bounded address injectivity forces i=b and q=k. Since m<=k, the strict
gate q<m is impossible. The TOP tie forces m=k. Thus b<j,
y=p(k,j,k), and B(b,j)=true.

The reverse presentation would give y=p(k,i,q) and
p(k,b,k)=p(k,j,m), with i<j and q<=k. Bounded block order then gives
y<p(k,b,k), contradicting the initial strict order. No ordinary symmetry
is needed for this directed positive-neighbour decoder.

The decoder itself is valid even when k=0. The coherence argument below
requires k>0 so that the generation-zero coordinate is strictly old.
For a genuinely eligible original v in the finite structure,
`p(k,b,k)+1<=freeLevel(v)<=v` provides the required strict order.

## 2. The entire eligible TOP column copies generation zero

Fix k>0 and the actual finite numerical-H structure A on Fin N.
Let `Stage=hStageOriginals K k N U J`, with `J subset Plan`, the bounded
dummy-root contract, the bounded positive-free-level Plan-role contract,
and `ResolvedQChronologicalAxioms role E`. Assume the tested base b has
`ResolvedQOmittedBase (role b)` and c=p(k,b,k)<N. Put q=p(k,b,0).

For every actual stage original v with c+1<=freeLevel(v), prove

    L_A(c,v)=L_A(q,v).

Eligibility at c implies eligibility at q because q<c.

* If L_A(c,v)=true, the new TOP decoder gives a later TOP original
  v=p(k,j,k) with E(b,j)=true. The existing bounded stage-role theorem
  also identifies it as a selected coded TOP. The generation-zero-to-TOP
  gate is open since k>0, so L_A(q,v)=true.
* If L_A(q,v)=true, the existing lower-real decoder at generation zero
  gives a later base j>b, a bounded generation 0<m<=k, and E(b,j)=true.
  The whole-stage omitted-base role theorem forces m=k. Now the
  TOP-to-TOP tie is open, so L_A(c,v)=true.

These two positive implications give literal Boolean equality, including
when both bits are false. No assumption that all names are real is made:
a positive bit supplies its genuine bounded real presentation. Roots,
retained auxiliary originals, and every other eligible stage name remain
in the universal quantifier.

## 3. Complete old-to-next coherence

For two eligible stage originals v,w, equality of complete old types at c
includes equality of the actual ordinary bit at q<c. Section 2 identifies
that bit with each cut bit. Thus the cut bits agree. Ordinary symmetry,
forward E=true and reverse E=false from eligibility, and the common socle
then let `full_equal_ordinary_cut_column_determines_next_type` establish
complete next L+/E equality at c+1.

Combining this TOP case with the published strictly lower positive case
gives a useful unified implication for every `0<g<=k`. The case split is
`g<k` versus `g=k`. Generation zero is deliberately not included.

## 4. Full structural exclusion for arbitrary represented seeds

Let X be any actual seed family represented by the root originals U;
in particular X may be all planned cap ancestors. At the true stage
J=Run.I(c+1), assume no seed ends at c and the actual descending Plan
inclusion. The general whole-stage structural lift applies to Section 3
and derives both no-I1 and no-I2 in the full pre-cut closure. It includes
generated parameters and meets, endpoints and self-meets. Neither
structural verdict is a premise.

At a TOP cut, k>0 makes c>0. At a unified positive-generation cut,
g>0 similarly makes c>0. For planned cap ancestors, c outside Plan
supplies the no-seed-at-c premise directly; the new theorem must keep
its generic seed-representation input rather than silently reuse the
smaller literal TOP-prefix seed family.

## 5. Actual TOP nonselection

Under the usual Henson simplicity, symmetry, clique avoidance and
height bound, and with the actual top seed and c<top, the published
`henson_actualRun_nonstructural_selected_has_lower_real_cut` says that
a selected positive cut with no-I1/no-I2 must equal p(k,j,g) for some
g<k. Apply this after the structural exclusions of Section 4.
If the tested cut is p(k,b,k), bounded injectivity would give k=g,
contradicting g<k. Hence the actual TOP cut is not in Run.I(0).

This uses the existing full-source B3 result through its established
actual-run classifier. It does not infer structural boringness merely
from TOP B3. No additional chosen marked-B3 assumption is needed at
these TOP cuts.

If the exact-plan induction requires noninterestingness explicitly,
a hypothetical interesting actual pre-cut closure inserts c into
Run.I(c) by `interesting_step`, and the final-tail identity puts it
in Run.I(0). The proved nonselection contradicts that conclusion.
The c<top hypothesis remains necessary in this adapter.

## Adversarial checks

1. TOP-to-TOP ordinary edges are allowed; the proof uses that tie rather
   than declaring TOP cut-stars empty.
2. The old lower-cut decoder cannot be applied at g=k; the exact TOP
   generator analysis is a separate lemma.
3. Every decoded generation is bounded by k, so no address-alias issue
   is introduced.
4. Eligibility, not merely a real address, gives strict source chronology.
5. Reverse generator orientation is excluded by actual block order.
6. The equality of whole columns uses both positive directions and hence
   covers false bits as well.
7. k>0 is essential for q<c; the raw decoder's k=0 case is not mistaken
   for a positive-generation coherence theorem.
8. The entire eligible current-stage pool is quantified, not a marked
   selected tuple or a final pool guessed before descending induction.
9. The omitted-base role and actual J subset Plan hypotheses remain;
   a retained auxiliary TOP need not satisfy this claim.
10. Complete L+/E types, negative old atoms, and seed absence are retained.
11. TOP B3 alone is insufficient; the structural implication is derived
    separately before applying the actual-run lower-real classifier.
12. This closes the TOP branch of the finite omitted-cut partition, not
    the infinite resolved-Q construction or the record-dependent age
    invariants at lower real cuts.
