# Track F — genuine independent-code vertex from a rank-zero actual target fibre

21 November 2026. English argument and adversarial audit **before Lean**. Next step after verified K4 tuple synchronization (lean-kk PR #410) toward the actual cover/split/code-history lower bound. Frozen black manuscript unchanged.

## Precise statement

Fix any actual source and target ordinary-edge tables `E_s,E_t` and an **injective induced** map `e:ℕ→ℕ` (not order preserving). Fix genuine source and target finite Henson one-types `u,v`. Suppose `rank(u)=0` (manuscript singleton rank 1) and the **actual** source coding-node fibre

`A(v) = {x : IsCodingNode(x) ∧ level(v)≤e(level(x)) ∧ target image's complete two-sided prefix bits realize v}`

is `0`-large above `u`.

Let `P` be **any finite set of previously selected source originals**. Assume that if `p∈P` already belongs to the old domain of `u` (i.e. `p<u.level`), then the bit of `u` at `p` is **zero**. This assumption is indispensable: a positive bit fixed in the original type cannot be erased by refinement. The vertices of `P` above `u.level` need no initial restriction. Fix any target cutoff `B`.

**Conclusion.** There is a GENUINE actual source coding one-type `x`, extending `u`, whose original vertex index is `r=x.level`, such that:

* `x∈A(v)`; hence `e(r)` is an actual source-image vertex realizing the prescribed target type `v`;
* `e(r)>B`, despite e being nonmonotone;
* every p∈P lies below r, and `E_s(p,r)=E_s(r,p)=false`;
* `E_t(e(p),e(r))=E_t(e(r),e(p))=false` for every p∈P, using inducedness on distinct indices;
* the selected source coding type has rank 0 (optional rank normalization).

Thus one rank-zero independent code can be chosen later than all target events, avoiding every previously coded vertex in **both orientations**. It is only the local coding-vertex step; it does not by itself preserve the other active fronts or show the absence of unrecorded mixed-profile events.

## English proof

Because e is injective, the preimage of the finite target set `{0,…,B}` contains at most B+1 source indices. The previously verified theorem `HensonOneType.injective_eventually_beyond_target_prefix` (Track F nonroot prefix fibre) produces `M_e` such that `a≥M_e ⇒ e(a)≥B+1`.

Let `M_P=1+max P` (or 1 if P is empty), and take `H=max(u.level,M_e,M_P)`. Set `z=zeroPad(u,H)`. The complete chronological type extension `u≤z` agrees on both positive and negative bits before `u.level`, and has **zero** positive bits at every coordinate in `[u.level,H)`. It retains rank zero. The verified `RankLargeness.large_mono_cone` gives 0-largeness of the SAME actual target fibre A(v) above z. The verified `large_has_member` produces an actual coding type x∈A(v) with z≤x.

Since `x.level≥H≥M_e`, the target image satisfies `e(x.level)≥B+1`. Since every p∈P has p<H, we have p<x.level. To prove p is a nonneighbour of x: if p<u.level, the old-zero hypothesis says p∉u.neighbours; if p≥u.level, p∉u.neighbours by u's genuine finite-prefix bound. Thus p∉z.neighbours (its neighbour set is literally u.neighbours). Chronological extension z≤x preserves every bit below H, hence p∉x.neighbours. Because x is an **ACTUAL coding node**, both directed source graph bits from p to x.level equal `decide(p∈x.neighbours)=false`.

Finally, p<x.level makes the source indices distinct, so inducedness transports the two source zeros to `E_t(e(p),e(x.level))=false` and `E_t(e(x.level),e(p))=false`. Since rank(x)≤rank(z)=0 by actual rank antitonicity, rank(x)=0.

No clause uses `e(a)≥a` or transfers source order to target order. No new vertex is invented outside the actual coding fibre.

## Hostile audit (what is *not* automatically proved)

1. The finite-preimage cutoff needs injectivity of e. Without it, e could send arbitrarily late source originals into a single old target coordinate.
2. We need **B+1**, not merely B: this makes the image strictly later than B rather than merely at or later.
3. The selected source type must be actual, not a merely consistent hypothetical type. `sourceCodingFibre` includes `IsCodingNode` by definition.
4. Largeness of A(v) must remain large after source zero-padding. This follows from the verified rank-preserving cone-monotonicity, not from arbitrary subset density.
5. Previously coded vertices p<u.level must already have zero bits in u. That invariant is maintained by later zero-padding, but cannot be inferred from rank(u)=0 alone.
6. Previously coded p≥u.level are handled by the new zero-pad interval. The lemma must not assume all old coded vertices were initially below u.level.
7. The source coding original r=x.level is **at or beyond** H, not the level H itself.
8. The target original image e(r) is later than B even if e reverses or scrambles arbitrarily many finite indices.
9. The two graph orientations must both be zero; `IsCodingNode` supplies exact two-sided old-bit agreement and inducedness transports both.
10. The old source p and new selected r are distinct because p<H≤r, so off-diagonal inducedness applies correctly.
11. The target old type v does not need to be of rank zero for the selection theorem. For the manuscript's independent code, one has initial rank(v)=rank(u)=0 by compatibility.
12. The graph need not be assumed K4-free or one-point left-dense **again**: the inputs are already genuine finite types with a rank-zero large actual coding fibre.
13. A finite set P could include repeated target-image coordinates only if e were noninjective; injectivity excludes this. P itself is a Finset.
14. This local coding lemma does NOT prove that any remaining active target fibres survive after the chosen code. They must be zero-padded on the source side and synchronized again using the verified tuple theorem #410.
15. It does NOT automatically establish an independent-code **event** in the canonical target history, whose pre/post profiles and unrecorded cuts still require the sandwich argument in the frozen manuscript.
16. It does NOT prove full cover/split history realization, diary unavoidability, or BRD degrees.

## Lean acceptance gates

Write a named theorem using the existing genuine `HensonOneType`, `sourceCodingFibre`, `injective_eventually_beyond_target_prefix`, `RankLargeness.large_mono_cone` and `RankLargeness.large_has_member`, with proof of both source and target zero columns to every p∈P. Provide a strict named standard-only transitive axiom report and exact-head Lake build. After it passes, develop the **survivor zero-padding**/resynchronization step separately. Do not promote the global history-realization marker.
