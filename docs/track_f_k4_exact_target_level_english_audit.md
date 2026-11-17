# Track F — exact prescribed target level for K4 singleton compatibility

17 November 2026. English-first proof and hostile assumption audit before Lean.

## Dependencies (not yet both certified at note creation)

1. `Kk.TrackFK4FullSingletonTransport` (draft #312): conditional rank-large actual sourceCodingFibre of an arbitrary genuine source HensonOneType 4, normalized K4-free target graph, and arbitrary injective INDUCED (not order preserving) index map. It produces, at every TARGET lower bound L, a source same-rank refinement and an actual target type `w` at some level >= L with target rank exactly source rank and still-large actual source fibre.
2. `Kk.TrackFExactTargetPrefixRestriction` (draft #313): genuine exact target type restriction to a chronological prefix L, safe K3-neighbourhood, full bit-preserving target type extension and rank sandwich for equal endpoint ranks; the sourceCodingFibre of longer target type is contained in the shorter type's fibre.

## Exact-level theorem

Fix actual target/source `HensonOneType 4`, an arbitrary injective induced graph embedding `e:Nat→Nat`, normalized K4 avoidance of target graph, and an INITIALLY compatible pair `(u,v0)` with `rank v0 = rank u` and the ACTUAL source coding fibre of `v0` rank(u)-large at u. For every exact target level `L >= v0.level`, obtain a type `vL` with **vL.level = L** and `v0 <= vL`, and a same-rank source refinement `uL>=u` with `rank uL=rank vL=rank u`, such that the new ACTUAL coding-node fibre of vL stays rank(u)-large at uL.

Proof: Apply the verified all-K4 SAME-RANK continuation at target cutoff L, producing `w>=v0` at level≥L, plus uL. Set vL=restrictPrefix(w,L). Since v0<=w and its level is ≤L, v0<=vL<=w. Rank antitonicity gives `rank(w) <= rank(vL) <= rank(v0)`; both endpoints have rank(u), hence vL has rank(u). Every actual coding original whose target image column realizes w automatically realizes vL, so `sourceCodingFibre(w) ⊆ sourceCodingFibre(vL)`. Monotonicity of recursive Large under set inclusion transfers the already verified rank-large source fibre to vL.

**Why this is not vacuous:** A target type over a long prefix need not admit an actual coding original at the earlier index L. The manuscript asks for an exact target TYPE, not an actual original at L. Restricting the genuine Henson one-type (retaining its K3-free old-neighbour certificate and all 0/1 bits) is exactly the right object.

## Positive rank drop

The second clause of the manuscript `lem:independent_lower_transport` only asks for a target level beyond an arbitrary bound, not exact-level. The already verified positive-rank-drop theorem of #312 directly implies it once source type rank s>0. Its INITIAL target rank equality is not required by the stronger rank-drop theorem (only source fibre largeness). Thus no second truncation is necessary for rank drop.

## Hostile checks

1. Exact target L≥level(v0) is essential; restriction below the old level could destroy v0's complete prefix.
2. The rank sandwich requires `rank(v0)=rank(w)`. A merely rank-large source fibre without initial target rank agreement is insufficient for this *exact-level* rank conclusion.
3. Prefix restriction must not create a new positive bit at a formerly zero old coordinate; full `HensonOneType.Extends` requires 0-bit agreement too.
4. Actual target prefix safety derives from finite directed clique capacity monotonicity; do not assume arbitrary binary colour patterns are consistent.
5. Source coding fibre inclusion goes from LONG to SHORT prefix, not vice versa. Moving from w down to vL enlarges the set of source coding witnesses, preserving largeness.
6. The embedding e need not preserve original enumeration order: this exact-level lemma inherits the injective-induced hypothesis only from the all-K4 continuation theorem.
7. The source type uL is a genuine consistent source type, not necessarily an ACTUAL coding original; the fibre itself continues to consist of genuine actual original-vertex coding nodes.
8. This is one-coordinate singleton age/rank transport, not a multi-sort Ramsey diary proof. The full K4-free BRD theorem, full synchronized tuple profile and non-precompact diary match remain pending.
9. `OnePointLeftDense` appears in the earlier actual coding-node root-denseness theorem, but the conditional compatibility continuation only assumes fibre largeness; do not silently add stronger source enumeration assumptions to the manuscript's general embedding theorem.

## Formalization acceptance

After #312/#313 exact-head named gates PASS, compile the exact-level theorem and a uniform positive-rank drop corollary under the same external input assumptions. Confirm exact theorem names, actual source coding-node predicates and single-rank scope in `#print axioms`. Keep black TeX frozen and full multi-sort validation pending until verified.