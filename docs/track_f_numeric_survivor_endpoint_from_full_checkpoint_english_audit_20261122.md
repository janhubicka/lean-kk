# Track F — derive real target survivor NUMERICAL endpoint equality from the previous full checkpoint

22 November 2026, evening. English proof and hostile audit BEFORE Lean. This directly discharges the remaining endpoint equality input in the non-dummy pre-code age rigidity theorem merged as Track F PR #488.

## The genuine input invariant

Take an actual source ordinary graph Esrc, an actual normalized K4-free target Etgt, and an injective induced original-index embedding e that need NOT preserve enumeration order. At some previous checkpoint, let

  u : Fin(d+1) → HensonOneType(4,Esrc),
  v : Fin(d+1) → HensonOneType(4,Etgt)

be true finite one-type families at common respective source level m_s and target level m_t. Assume the SOURCE family u is injective, each target type v_i has the same genuine singleton rank as u_i, and the ACTUAL sourceCodingFibre of v_i is recursively rank(u_i)-large above u_i.

Crucially assume the checked full checkpoint invariant

  CanonicalAge_source(u,m_s) = CanonicalAge_target(v,m_t)

NUMERICALLY on EVERY bounded nonempty admissible support of Fin(d+1), including mixed triples. This invariant is constructed at real initial synchronization checkpoints by the already verified numeric source→target theorem (#482), but it is explicitly an input to a later history step rather than being inferred from mere rank matching.

Choose a coded sort j:Fin(d+1). Let r be an already selected ACTUAL source code original with r≥m_s. Its true target image is c=e(r); no monotonicity of e is assumed. Prescribe any later target cutoff B.

## Physical survivor synchronization after the code

Define f=Fin.succAboveEmb j : Fin(d) ↪ Fin(d+1), the exact order-preserving deletion in the TARGET sort order. Let

  uS_i = u_{f(i)}, vS_i = v_{f(i)}.

Every input hypothesis (source injectivity, common level, actual fibre largeness, and singleton rank compatibility) is inherited by these actual survivor subfamilies; repeated sort labels remain possible in abstract future graphs, but the one-types uS themselves are distinct as required by synchronization.

Apply the previously verified physical K4 survivor-synchronization theorem (#433) with r≥m_s. It produces later levels M,H and ACTUAL source/target surviving types w,t on Fin(d), with B<H, c<H, common source/target levels, true rank preservation, target prefix extension vS_i≤t_i, all target bits at c ZERO, target tuple injectivity, actual coding-node fibre largeness above w_i, and universal finite K4 class equivalence of the ORIGINAL SOURCE survivors uS and LATER TARGET survivors t.

Apply the independently verified finite class→numerical age extraction (#478/#482) to conclude the exact NUMERIC equality

  CanonicalAge_source(uS,m_s) = CanonicalAge_target(t,H).

## Restrict the old full checkpoint invariant to the TRUE survivors

The verified physical normalized canonical survivor reindexing (#475) gives, on every nonempty support U⊆Fin(d),

  CanonicalAge_source(uS,m_s)(U)
    = CanonicalAge_source(u,m_s)(f[U]),
  CanonicalAge_target(vS,m_t)(U)
    = CanonicalAge_target(v,m_t)(f[U]).

The assumed numerical equality of the old FULL source and target checkpoint ages therefore gives

  CanonicalAge_source(uS,m_s)
    = CanonicalAge_target(vS,m_t).

Combine with the just-proved numerical survivor endpoint result from #433/#482:

  CanonicalAge_target(vS,m_t)
    = CanonicalAge_target(t,H),

on EVERY support, including triples.

This is a theorem DERIVED from one source–target invariant and an ACTUAL survivor synchronization construction, not a postulated equality of the selected intermediate target fronts.

## Outputs

Return H,M, actual source survivor refinements w, and actual target survivor refinements t with all real stage invariants preserved; importantly include the FULL NUMERICAL endpoint age equality above. This can be fed directly into the checked non-dummy pre-code age rigidity of PR #488, after constructing the true pre-code image front at c.

The selected code vertex r need not be constructed again here; its existence and past-zero columns are independently checked in #424. This theorem handles the WHOLE surviving target family, not the coded branch.

## Adversarial audit

1. The full source–target checkpoint age equality is a real induction invariant, NOT a consequence of rank equality alone. It must be an explicit premise.
2. All numerical ages are canonical integer-witness ages of genuinely safe Henson fronts. Raw support bounds may contain redundant inequalities and are not asserted numerically equal.
3. Initial source one-types must be pairwise distinct at common m_s, so their true survivor subfamily is also injective.
4. Initial target v types may have coincidences in the general synchronization construction, but the previous genuine diary checkpoint normally has distinct types. The numeric endpoint theorem does NOT silently assume target injection.
5. The surviving sort map is exactly Fin.succAboveEmb j. It is injective and preserves the intended TARGET order of labels; it does not preserve source order unless this is separately an invariant.
6. The source index r is required to be ≥m_s to safely zero-pad survivors after it. In an actual code selection, this follows from u_j≤x and r=x.level, not from source/target enumeration monotonicity.
7. The code image c=e(r) need not be ≥r. All target zero-bit and later-cut inequalities use c.
8. Actual after-code synchronization #433 supplies target old extension vS≤t and target zeros c; do not infer these from finite class equality alone.
9. Real actual sourceCodingFibre largeness (not hypothetical cones) is essential in #433 and retained in the output for further diary induction.
10. The numerical target old/later equality holds on all admissible nonempty survivor supports, including mixed triples and repeated sorted graph labels, because #482 extracts FULL ages from universal finite classes.
11. The full checkpoint equality is reindexed on BOTH source and target with the SAME injection f. Matching unlike source/target lexicographic orders would be unsound.
12. The theorem does NOT create a future dummy coded branch; the output only contains the real survivors on Fin(d).
13. It does not assert the full pre-code age is already equal F. That is derived only AFTER constructing a true intermediate pre-code target type and using the code singleton + legal zero-code law in #488.
14. It does not prove existence of the selected code r, its edges to the finite past or its actual source image colour. Those are separate already-verified #424 hypotheses/conclusions.
15. It does not prove a target lexicographic diary type-order invariant; the real history application must supply its coordinate encoding.
16. It does not prove complete cover/split/code histories, dependent Kpt L+/E/B3 records, 24 orbit counts, or a global big Ramsey degree lower bound.
17. Empty survivor set d=0 works: all numerical age functions on empty admissible domains are equal, no Fin(0) element is used.
18. No frozen black manuscript prose is modified, and global history-realization validation remains pending.

## Formalization gate

Prove a single named theorem assembling:
- exact Fin.succAboveEmb j restriction of the genuine input type families;
- existing physical after-code K4 survivor synchronization #433;
- checked numeric extraction from all finite K4 graph classes (#478/#482);
- checked canonical survivor reindexing #475 of the old FULL checkpoint equality.

Return the true later source/target survivors, their genuine rank/large/zero bit properties and the exact numeric OLD-TARGET/LATER-TARGET survivor canonical-age equality. Dedicated exact-head Lake build, strict standard-only axiom gate and full Lean CI. Never assert the desired endpoint equality as a hypothesis.
