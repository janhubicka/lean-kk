# Track D — an unmarked strictly higher-generation physical original on the SAME I3 forbidden clique
16 November 2026. English-first correctness proof, then hostile audit, BEFORE Lean.

## Verified exact dependencies

- The merged and centrally visible `Kk.ActualRunStructuralOrLowerReal.henson_actualRun_nonstructural_selected_has_lower_real_cut` proves that a genuine selected positive nonstructural (I3) cut in ONE finite Henson numerical-H AlgorithmRun equals `hPosition k idx g` for `g<k`. Its hypotheses are the complete actual pre-cut closure's absence of I1 and I2, a top seed, the ACTUAL `Run.I (cut+1)` and the actual finite Henson original pool.
- The merged `Kk.B3ActualI3UnmarkedSameClique.henson_actualRun_I3_good_marked_has_unmarked_inside_same_clique` gives a stronger obstruction than merely an unmarked full source name. Given a represented, cut-eligible, corrected-B3-good marked source, one genuine forbidden clique of an L-only B3 age witness has an upper vertex whose type is witnessed by a full-closure physical original **not** in Marked, with the COMPLETE (cut+1) ordinary-L type absent from the Marked pool's actually CHOSEN upper L outputs. Source name/cut eligibility/positive cut edge are explicit, and this does not infer E on arbitrary L-only witness vertices.
- The merged `Kk.PhysicalLowerRealCutNeighbour.finiteNumericH_eligible_lower_cut_neighbour_is_higher` proves that any actual free-cut-eligible positive physical L neighbour at a non-top real cut `hPosition k idx g` necessarily comes from a STRICTLY LATER base `j>idx` and STRICTLY HIGHER generation `m>g`, with the literal original graph bit `E(idx,j)=true`. This is about a genuine finite numerical-H ORIGINAL, not about all arbitrary future L-only witness vertices.

All three dependencies are already merged; the full Lean main head at the start of this work is `1753f46ef115046cb5bc8d88ed14f5d0d61c04ed`, [completed successful workflow 43762014560](https://github.com/janhubicka/lean-kk/actions/runs/43762014560). The new theorem will still get its OWN exact-head dedicated strict gate.

## The statement

Fix `ell>=2`, `ell<=k+1`, a symmetric irreflexive K_ell-free Boolean graph `E`, a finite numerical-H model of carrier N, a genuine seed set X represented by U, a genuine AlgorithmRun with actual top seed, and a selected positive nonstructural cut c where 0<c<top,N. Its actual pre-cut full Kpt closure Z is computed at `Run.I (c+1)`; its final maintained original-name carrier is computed at `Run.I 0`. Let P be the exact `actualHensonRunCutOccurrence` with full closure-selected original names and no I2.

Assume Marked is a represented subset of actual physical source names, with at least one cut-eligible member, and that the actual Marked chosen prescribed source passes corrected B3. (These remain application hypotheses, NOT known properties of the selected macrodiary.)

Then there are `g,idx` with `g<k`, `c=hPosition k idx g`, one ordinary-L finite age model V and ONE forbidden `K_ell` copy `e` in V containing c, and a vertex `e(a)>c` of that SAME clique with an actual physical original name `v:Fin P.M` satisfying:
1. `P.Full(v)`, `not Marked(v)`, and actual free cut `c+1 <= P.ambient.freeLevel(P.original(v))`;
2. actual positive physical ordinary-L adjacency `P.ambient.L.binary(c,P.original(v))=true`;
3. the COMPLETE directed next-cut ordinary-L type of `e(a)` is exactly the physical type of `P.original(v)`, which is absent from ALL *chosen* Marked upper outputs;
4. the SAME name `P.original(v)` has exact physical address `hPosition k j m` for `idx<j` and `g<m<=k`, and `E(idx,j)=true`.

Retain the original clique certificate's bounded carrier, old-socle equality, deletion avoids family, and every upper V vertex belongs to the SAME clique. Thus this is a genuine same-one-clique later-base/higher-generation missing-type obstruction, not two unrelated existential witnesses glued together.

## English proof

1. Apply the verified selected nonstructural `I3 -> lower real cut` theorem to the ACTUAL AlgorithmRun, obtaining `g,idx,hg,hGen`. No generation premise is guessed.
2. Apply the verified `henson_actualRun_I3_good_marked_has_unmarked_inside_same_clique` to that SAME true AlgorithmRun and original pool, and the specific Marked representation/nonempty/good hypotheses. Its conclusion is the exact `P.HasUnmarkedMissingSameCliqueCore Marked`; unpack the witness `V,e,a,v` with full source membership, exclusion from Marked, actual eligible positive cut edge, complete ordinary-L next-cut equality and missing Marked chosen type. No auxiliary E is assigned to V.
3. Apply `finiteNumericH_eligible_lower_cut_neighbour_is_higher` to the SAME `P.original(v) : Fin N`, at `hPosition k idx g`. The numeric source cut equality `hGen` transports the already verified free-level inequality and actual positive physical L bit from cut c to this exact real coordinate. The theorem yields `j,m` with later base/higher generation and exact base E bit. No choice of a different name or different forbidden clique.
4. Rebuild the enlarged clique certificate with the SAME `V,e,a,v`, adding the `j,m` pair. This proves everything claimed.

The only new reasoning is quantified composition of three independently checked exact statements, but the composition prevents an important possible bug: a higher-generation original found *elsewhere* in the pool would not necessarily witness the SAME offending clique/complete missing selected type.

## Hostile audit — 18 items

1. Do not swap `Run.I(c+1)` with `Run.I 0`; the former defines Z, the latter only the final carrier.
2. Do not replace the genuine full original predicate by selected diary active branches. The original name may be a q2-type auxiliary parameter, exactly as in the K4 cut-10 regression.
3. The source Marked must be **represented in Z** and its actual chosen profile must be corrected-(B3)-good. These are assumptions and are NOT silently deduced from equality of selected graph-age capacities.
4. The current same-clique theorem assumes an eligible Marked witness. Even though a separate finite transfer removed marked-source nonemptiness in a different implication, it does not discharge this theorem's exact hypothesis.
5. The actual nonstructural I3 theorem requires no full I1 endpoint and no full I2 meet, positive cut c, and an actual top seed. Preserve every one.
6. The checked numeric location theorem uses `ell<=k+1`; do not confuse K_ell with manuscript k or claim the theorem for arbitrary k=0.
7. For a physical positive edge on a real non-top cut, the original is necessarily a LATER base, not just a higher generation of the same base.
8. The generator's exceptional top/top edge gate is real; it is excluded only by `g<k` after the full clique relocation theorem.
9. The ordinary L type equality includes both directed atoms and negatives. Positive crossing alone never implies equality of chosen marked next-cut outputs.
10. Keep the exact Marked chosen-output *absence* on the SAME `v`; do not drop this predicate.
11. Retain `V.Realizes cliquePattern e` and the same-clique upper-vertex condition; otherwise the theorem becomes a weaker independent existence claim.
12. The W/V witness is a finite **ordinary-L** model; no fake E edges or E-socle predicates are installed on its arbitrary future vertices.
13. The true physical original v has aux E/free level; use `P.ambient.freeLevel(P.original(v))`, not the arbitrary V witness's nonexistent auxiliary free level.
14. The proof of higher numeric location needs `P.original(v) : Fin N`, not a bare Nat lacking carrier membership. This exact type is provided.
15. Cut equality is oriented carefully: `cut=hPosition k idx g`, so rewrite to the physical position in both hFree and hEdge.
16. Nothing here bounds all structural I1/I2 levels by the manuscript's retained I, or constructs the common G+ labelled inverse-source orbit.
17. This is a NECESSARY local I3 obstruction, not a sufficient criterion for I3 or an unconditional BRD count. It is not a new selected-front graph-age loss theorem.
18. Check exact qualified axiom reports and actual imported proof code at the new HEAD. Do not promote into a central paper marker until its own gate passes.

## Next application bridge

For a specific small-independent record and its retained full source, prove that **no** genuinely full cut-eligible name of a later base/higher generation at any omitted nonstructural lower-real cut can satisfy ALL of:
- positive physical base E adjacency to the cut,
- selected source exclusion (`not Marked(v)`), and
- complete chosen upper-type absence from the Marked source on one forbidden clique.

If that prohibition is proved from the actual Q block schedule plus physical parameter-closure normal form, the present theorem eliminates all omitted nonstructural I3 cuts. Structural odd/even I1/I2 cuts still require independent full indexed analysis; this is not yet complete boringness.

## Lean execution plan

Create `Kk/B3ActualI3UnmarkedHigherGeneration.lean` importing the THREE checked modules. Define `HensonCutOccurrence.HasUnmarkedHigherGenerationSameCliqueCore` as the existing exact `HasUnmarkedMissingSameCliqueCore` witness with the **same** omitted physical original v carrying the additional higher generation / later base certificate. Prove the new theorem with a real actual-run P and all quantifier hypotheses spelled out. Register the exact qualified name in a dedicated direct module build and strict transitive axiom gate. If the proof has an error, repair English first.
