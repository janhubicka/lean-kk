# Track F — actual pre-code target front at the selected image cut
22 November 2026. English proof and adversarial audit, committed BEFORE Lean. Next geometric bridge after the independently checked and merged code selection (#424), survivor synchronization (#433), zero-cut survivor ages (#447), true-age consistency (#436), and chronological age sandwich (#438).

## A concrete, previously missing object

Fix genuinely normalized K₄-free target edge table `E_t`, source table `E_s`, and an arbitrary original-index map `e : ℕ→ℕ`. Let `old_i`, indexed by `Fin(d)`, be DISTINCT genuine target Henson one-types at the SAME old level m. Select one code index `j` with `rank(old_j)=0` (manuscript singleton rank 1). Let `x` be an ACTUAL source coding one-type in `sourceCodingFibre(E_t,e,old_j)`, with source coding original `r=x.level`, and let `c=e(r)`. Fibre membership guarantees `m≤c` and both complete old target column equalities.

For every i≠j, suppose a genuine later surviving target type `later_i` extends `old_i`, reaches at least level c+1, and has zero bit at c. These are the properties provided by the verified survivor synchronization after selecting r, except that the survivor index set is represented here by one COMMON `Fin(d)` family with an unused placeholder at j. The placeholder needs only to be a genuine type of sufficient level and is NEVER read in a conclusion about survivors.

**Claim:** construct an entire genuine PRE-CODE target front `pre_i` at the exact cut level c, with:
1. `pre_j` is the genuine ACTUAL target old-column type of the selected target original c, not a hypothetical proxy;
2. `old_i≤pre_i` and every `pre_i.level=c`; hence complete old positive AND negative bits are preserved;
3. `pre_j.rank=0`, and its **canonical normalized graph-age singleton** has value exactly 1;
4. `pre` is pairwise injective, since old target types were already distinct at common level m;
5. for each i≠j, `pre_i≤later_i`, and its exact positive-neighbour set equals the genuine later type truncated to level c+1 (because the later bit at c is zero);
6. the complete actual canonical integer age of `pre` is GENUINE, and its every support value is ≤ the complete original target canonical age. This is the exact physical premise needed for the precode rigidity theorem (#430).

No sorted diary assertion is assumed, and no equality of pre-code and original FULL ages is asserted yet. The survivor restriction equality and legal zero-code condition are separate endpoints to be composed later.

## English construction and proof

Set `c=e(x.level)`. Define the coded target type
`q := targetTypeOfOriginal(4,E_t,c,c)`, with `c≤c` reflexive.
The existing physical theorem `targetOldNeighbours_safe` derives K₃-free safety of `q.neighbours` from the true normalized K₄ forbidden-family axiom, so q is genuinely a Henson one-type. The existing `targetTypeOfOriginal_columns` proves BOTH actual directed old-edge columns of the original c coincide with the complete neighbour bits of q. The true coding-fibre membership of x over old_j proves `old_j≤q` through `targetTypeOfOriginal_extends_old`. Rank antitonicity along the extension then gives `rank(q)≤rank(old_j)=0`, hence `rank(q)=0`.

For each surviving i≠j define `p_i := restrictPrefix(later_i,c)`, using c+1≤later_i.level. Put `p_j=q`. This yields one honest family p indexed by the original labels. All levels are exactly c. For the code index, old_j≤p_j; for every survivor, old_i≤later_i and m≤c imply old_i≤p_i by verified exact-prefix restriction. Likewise p_i≤later_i for survivors. The verified zero-cut lemma (#447) shows
`N(p_i)=N(restrictPrefix(later_i,c+1))`
for every survivor, because c∉later_i.neighbours.

Injectivity is not automatic from the later target types: two earlier old target types could become equal under arbitrary re-labelling if we erased old bits. Here we do not erase any old bit. If p_i=p_k for distinct i,k, the complete bit equality on the original prefix [0,m), inherited from old_i≤p_i and old_k≤p_k, would show old_i=old_k by genuine one-type field extensionality. This contradicts injectivity of old. The existing source-bit separator lemma (#407) is an equivalent formulation.

By verified actual-front age positivity (#436), the complete normalized integer canonical age `P` of p is a genuine graph age. By verified full chronological antitonicity (#438), `P≤F_old`, since each old_i≤p_i and old.level=m≤c.

To certify the coded singleton age, the raw singleton bound at p_j is
`3 - cliqueCapacity(E_t,N(p_j))`.
The genuine safety certificate says capacity<3. The genuine zero-based rank definition says `rank(p_j)=3-capacity-1=0`; thus capacity=2 and the raw bound is 1. The true raw bounds are support-monotone (#395), and verified normalized singleton canonicalization (#? `trackFCanonical_singleton_eq_raw`) therefore yields `P({j})=1`. This proof NEVER assumes that the raw table is numerically equal to its canonicalization on mixed supports.

## Hostile audit / remaining gaps

1. The code node x MUST belong to the **actual** `sourceCodingFibre` (not just a hypothetical consistent type). Its membership includes the exact two-direction target old columns. Without it the old-code-to-q extension can fail.
2. Target K₄ forbidden-family avoidance is required for `targetTypeOfOriginal` safety; it cannot be inferred from mere membership in a target-column colour class.
3. No monotonicity of the embedding e is assumed or needed in THIS local theorem; `c=e(x.level)` is the actual image coordinate, not x.level.
4. We need m≤c from x's target fibre membership. Do not attempt to infer it from chronological monotonicity of e.
5. The old target family must already be injective at a common m; later injectivity at a common H alone does NOT imply earlier prefixes are distinct.
6. The old/code type rank is **zero-based Lean rank zero** = manuscript singleton age one. Treating these numbers as equal would introduce an off-by-one error.
7. The selected code q is a type **of level c** (before reading its own bit), not of level c+1. This is the correct pre-code/front level.
8. Surviving later types need only genuine prefix coverage `c+1≤later_i.level`, an old-type extension, and zero bit at c. They need not be generated by the same source enumeration order.
9. The unused `later_j` placeholder is irrelevant to all survivor conclusions; a future clean API can replace it with a true survivor subtype family to avoid gratuitous data.
10. At d=1 the survivor properties are vacuous; constructing a genuine old_j and q remains valid and does not invent a Fin(0) survivor.
11. Every old_i≤p_i is a COMPLETE chronological extension, including negative bits; mere containment of neighbour sets would be insufficient for the intended diary.
12. Mixed/two/three-sort canonical age is computed by the complete integer-witness canonicalizer, not by a one-point cardinality shortcut.
13. `P≤F_old` alone does NOT imply P=F_old. The pre-code rigidity theorem #430 additionally requires survivor support equality, which must be obtained by the endpoint sandwich after the surviving front is synchronized. This module must NOT assert it without proof.
14. The zero-code legal equation `F(T)=F(T.erase{j})` remains a separate hypothesis from the prescribed history; it is NOT deduced from rank zero alone.
15. The later code image c cannot be assumed to be the source original r numerically; any target fibre property must refer to c=e(r).
16. Unrecorded earlier age events still need the full three-front sandwich with matching endpoint profiles, and target lexicographic source-label reindexing remains independent.
17. The full Kpt dependent L+/E diary data, cover/split operations, numerical 24-case classification, and global BRD lower bound remain unproved by this local result.
18. Frozen manuscript black proof is untouched; promotion of any marker is allowed only for these precisely stated component implications after exact-head Lean/axiom CI succeeds.

## Formalization plan

Implement first the actual target **code prefix theorem** (q constructed from the actual image original with old-type extension, rank zero and exact two-directed columns), then the complete finite **pre-code front theorem** (genuine p and its injectivity, chronological extension, preserved survivor zero bits, true canonical-age consistency, full antitone bound and singleton canonical age one). Independently check standard-only transitive axioms for both; do not add axioms, sorry, or assume the desired pre-code age equality.
