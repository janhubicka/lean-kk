# Track F — exact compatible non-root transport at manuscript ranks one and two

17 November 2026. English-first proof, before Lean.
Prerequisites already verified and merged:
- #299: actual non-root target continuation preserving source
  rank and source-fibre largeness, with target rank<=source;
- #275: actual future target clique forces target singleton rank
  at least the size of that clique;
- #297: transported old source clique ensures the other inequality.
The first NEW one-source rank-two richness witness is in
draft #300; do not claim rank-two transport verified until its
actual edge lemma passes its exact-head gate.

## Rank normalization

Lean HensonOneType.rank is ZERO-BASED:
Lean rank 0 = manuscript singleton rank 1,
Lean rank 1 = manuscript singleton rank 2,
Lean rank 2 = manuscript singleton rank 3.

We prove the SAME-RANK continuation claim for Lean ranks 0 and 1.
This is the low-rank part of the olive `lem:independent_lower_transport`,
not its rank-drop statement or full arbitrary-rank theorem.

## Rank 0: complete without additional richness

Let source u have Lean rank 0 and sourceCodingFibre(v0) be
0-large above u, and let Etgt be normalized Henson and
e be an injective induced graph embedding.

For any target cutoff B, #299 gives genuine target vH,
source uH, v0<=vH, level(vH)>=B, u<=uH,
rank(uH)=rank(u)=0, and fibre(vH) 0-large above uH,
with rank(vH)<=rank(u)=0.
Since ranks are naturals, rank(vH)=0.
This proves exact same-rank non-root transport at
manuscript rank 1, conditional only on a preexisting large
source fibre, with no need for a source clique theorem.

## Rank 1: use the genuine edge richness witness

Suppose rank(u)=1 and fibre(v0) is rank1-large above u.
Apply #299 at a target cutoff beyond images of ALL old
neighbours of u. Obtain vH,uH with source rank1,
source fibre S_H rank1-large at uH, and target rank<=1.

The new genuine edge-richness theorem of draft #300 states
that S_H, consisting of ACTUAL coding vertices, contains
x,y∈S_H with x.level<y.level and
Esrc(x.level,y.level)=Esrc(y.level,x.level)=true.

The induced injective embedding maps these into DISTINCT
actual future target originals e(x.level),e(y.level).
They form an actual target edge in both orientations.
Because x,y both lie in sourceCodingFibre(vH), both
target images lie after vH.level and are adjacent
in both orientations to EVERY old target neighbour
p∈vH.neighbours. The target graph's normalized
Henson avoidance ensures K_ell-freeness.

Apply verified #275 to the target future clique of
size two. It says the target singleton MANUSCRIPT
rank is at least 2. Therefore target LEAN rank
is at least 1. Together with target rank<=1
from #299, this gives rank(vH)=1=rank(uH).

Thus the SAME-RANK continuation part of the olive
lemma is fully proved at manuscript rank 2 once
draft #300 and this composition are Lean verified.

## Hostile audit

1. The edge must be between actual coding original
   vertices, not hypothetical finite types.
2. Rank1 source largeness is essential to produce
   a two-vertex clique; rank0 largeness only
   guarantees nonempty coding members.
3. The two images are DISTINCT because e is injective,
   regardless of whether e preserves order.
4. Both target image originals lie AFTER the target
   cutoff by the definition of sourceCodingFibre.
5. The target future edge and its complete old join
   are both directed; inducedness and the two-column
   target fibre supply the necessary bits.
6. The source rank is the rank of ORIGINAL u and
   same-rank continuation uH. Target old-neighbour
   image bounds on the ORIGINAL u are already
   handled correctly in verified PR #299.
7. This result does not prove rank2 (manuscript rank3)
   transport; that requires TRIANGLE richness inside
   rank2-large actual source coding fibres.
8. It does not prove the rank-drop continuation
   statement, multi-sort compatible profile
   synchronization, or diary/BRD exactness.

## Lean plan

Implement rank0 transport immediately via #299.
After exact-head #300, import the actual edge theorem
and build the physical target W={e x.level,e y.level}
as a finite directed clique, prove its cardinality2,
its join to every old target neighbour, and apply
#275 plus #299. Strictly audit the theorem types and
transitive axioms. No global lower BRD validation
mark may be promoted.