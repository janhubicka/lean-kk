# Track F — private rank-zero descendants for any finite family of rank-large source types

18 November 2026. **English-first proof and hostile audit before Lean.**
The newly verified full finite sorted rank-zero realization theorem #355 may make the positive-rank richness induction much shorter than its current repeated maximum-rank splitting. We must first prove that one can assign **one rank-zero descendant per requested B vertex**, with pairwise disjoint NEW positive old-neighbour markers, even when the original source types have different ranks and repeat among requested labels.

## Basic lemma: descend all the way to rank zero

Let u be a genuine chronological Henson one-type of zero-based rank r and S an r-large set above u. By induction on r, there exists v≥u of rank zero with S 0-large/dense above v. For r=0 take v=u. For r=n+1, apply the defining recursive Large clause to u itself (as a same-rank extension) to get w≥u of rank n on which S remains n-large; apply the induction hypothesis to w. This uses NO additional graph-age or diary hypothesis.

Crucially this descent remains available ABOVE any prescribed chronological cutoff H: first zero-pad the ORIGINAL u to level max(H,u.level), preserving its rank and S-largeness. Descend from that padding. The resulting rankzero v has complete positive and negative old bits below H identical to u's original old bits.

## Globally private rank-zero daughters

Fix an arbitrary finite family of source requests indexed by Fin d, with genuine original root u_i (ranks may differ) and its own large coding-node set S_i. No equality of ranks or even distinctness of roots is assumed.

We choose one rankzero descendant v_i per request sequentially over the finite index set.

Suppose the requests in a finite set Q have been handled; their descendants v_j each have rankzero, S_j dense above them, and their new-marker sets
    M_j = v_j.neighbours \ u_j.neighbours
are pairwise disjoint.

For the next source request i, let H be greater than every previously chosen v_j.level and at least u_i.level. Zero-pad the ORIGINAL u_i to height H and then use the lemma above to find a rankzero descendant v_i≥zeroPad(u_i,H) whose fibre S_i remains dense. All fresh positive markers in M_i occur at indices at or ABOVE H: if p<H, the zero-padded source type has exactly u_i's old bits there, and v_i extends this padded node.

Every previous marker M_j lies STRICTLY BELOW v_j.level < H. Therefore M_i∩M_j=∅, even if u_i=u_j as genuine old types. The already verified real two-source zero-padding disjointness lemma (#283) is precisely this finite-set calculation.

Update the finite bookkeeping family and repeat for each request. At the end every requested vertex has a private rankzero daughter, all new-marker sets pairwise disjoint.

Finally set Hfinal to the maximum of all selected descendant levels. Zero-pad every v_i to Hfinal. This preserves each exact old-neighbour set, rankzero, S_i-density, and all pairwise new-marker disjointness, and provides the common source level needed by the full finite graph realization #355.

## Why this may bypass the maximum-rank induction

Suppose the original B has N labelled vertices with old parent sorts σ(a). Instead of assigning each parent to multiple lower-rank daughters and checking the split/untouched occupancy separately, create N **private sort labels**, one per vertex a. Each private sort's new root is a rankzero descendant of the original root u_(σ a). Its new-marker set is disjoint from all other private sorts' marker sets. Exactly ONE B vertex has any given private sort.

On every refined support of at least two different private sorts, the verified raw disjoint-marker collapse theorem (#259/#282) identifies the actual refined old common-neighbour raw age with the original raw age of the parent image support. The original B raw feasibility therefore proves every such clique admissible. On a singleton private sort the new raw age equals ONE (rankzero), and exactly one B vertex carries that sort, so its inequality holds automatically. This avoids any restriction on how many vertices were originally assigned to one parent sort and avoids a repeated maximum-rank induction.

Apply the now verified finite rankzero full graph realization #355 to the private refined sorts. Each selected ACTUAL original coding vertex is in S_(σ a), giving the desired labelled original-B graph realization. The proof needs no diary characterization.

## Hostile checks

1. **Ranks can differ.** Recursive descent works with each root's own rank; no uniform-rank source-front axiom is introduced.
2. **Repeat the original root as often as B has vertices.** The new request indices are distinct even when their original source root and large set coincide; temporal zero-padding still gives disjoint fresh markers.
3. **Rankzero roots may have EMPTY fresh marker sets.** That's fine. Two identical padded rankzero types can serve different private source labels because #355 chooses distinct actual coding original vertices by its induced chronological construction.
4. **Strict fresh separation:** each new-marker set M_i lies at or after the prior maximum H; previous M_j lie before H. Complete prefix preservation including negative bits is essential.
5. **No same-level source assumption for selection.** The initial family may have different heights; we pad each original separately. The B application requires the original source roots first synchronized at one level m, which is an explicit assumption of the paper's richness lemma.
6. **Raw support monotonicity:** for a multi-vertex B clique, the refined private-sort support has exactly those distinct vertex labels. Its image under the parent map is exactly the original set of sorts. Pairwise private-marker disjointness then gives equality of the correct RAW common-neighbour pool. Numeric CANONICAL mixed ages may differ, but feasible clique vectors are unchanged.
7. **No special treatment of untouched rankzero sorts:** one private sort per B vertex avoids splitting-vs-untouched bookkeeping. A rankzero parent receives no new positive markers, and repeated identical old roots are harmless because B's original singleton raw bound excludes edges among vertices of that sort.
8. **The private-source sort set is finite even when B is empty.** A Lean implementation may use Fin (N+1) to provide a harmless dummy sort; this cannot create a new graph constraint because no B vertex has that dummy label.
9. **Inducedness is not trivial from largeness.** The separate verified #355 finite construction does actual old-column, directed edge and nonedge checks vertex by vertex.
10. **Only SOURCE finite graph richness follows.** The source coding sets S_i may be target fibres, but matching complete TARGET mixed profiles, synchronizing distinct target types and diary-history unavoidability still require separate proof.
11. **No hidden OnePointLeftDense assumption.** This is conditional on S_i already being rank-large sets of ACTUAL coding nodes; the left-dense hypothesis is needed only for the independent root/root nonvacuity theorem in an arbitrary fixed enumeration.
12. **No unjustified certification.** The one-coordinate rank descent and finite private marker family must compile with correct Lean types and standard axioms before applying them to the paper's full richness statement.

## Lean acceptance

First prove the generic recursive Large→rankzero-dense descendant lemma, and its same-rank zero-padding variant. Then a finite-index simultaneous private zero-descendant selection with old-root-relative fresh marker disjointness and a common level. Explicitly preserve the rankzero-dense S_i hypothesis and the whole old-neighbour bits. Check each theorem's statement and standard transitive axioms in exact-head CI. Once verified, use the exact disjoint-marker raw-age collapse and #355 to prove the full original finite B source richness. Frozen black prose and global BRD validation marks remain unchanged.