# Track C — old full numerical H⁺ Kpt source survives extension of the BASE Henson original graph

**14 November 2026. English proof and 18 hostile checks BEFORE Lean.**
Stacked after [PR #140](https://github.com/janhubicka/lean-kk/pull/140) and [PR #145](https://github.com/janhubicka/lean-kk/pull/145), whose exact-head isolated and full-project CI both passed. This targets a genuine missing geometric step in the *recursive new-original* construction, not a rephrasing of fixed-K carrier truncation.

## Actual problem, dimensions and exact scope

A stage of the resolved-copy construction inserts fresh ORIGINAL Henson vertices. These insertions change the underlying base graph and thus potentially alter the L-part of its numerical H⁺. Previous Track C #140/#145 prove fixed-K, fixed-generation-k carrier N→M coherence. They do **not** address changing K itself.

Fix two age-test models K and L with the SAME signature db,du,dd and ONE fixed numerical generation k. Let b be the number of already fixed **base original blocks** and set

`blockStart(k,b) := hPosition k b 0 = 2*(k+1)*b`.

Let N≤blockStart(k,b), and N≤M. Suppose K and L have IDENTICAL:
- `K.binary i j r = L.binary i j r` for every `i<b, j<b`, every directed r;
- `K.unary i r = L.unary i r` and `K.diagonal i r = L.diagonal i r` for all i<b.

No relation is required for a new base original at index j≥b; its old backward column is allowed to be freshly chosen, subject to Track A/B's K-free test. In particular no equality `K=L` or equality of their carrier fields is required.

The old *numerical* carrier N must stop at/before the first H⁺ coordinate of base block b. Merely knowing `v<N` without this condition is insufficient: a numerical coordinate in the new b-th original block can depend on L's newly inserted base edges.

## C34: real positions below block start have old original addresses

If `x<hPosition k b 0` and `x=hPosition k i q` for any i,q∈Nat, then i<b. Proof: if i≥b then
`2(k+1)i+2q ≥ 2(k+1)b`; contradiction. In fact no q≤k is needed for this elementary lower-bound direction.

## C35: complete numerical L table stable on old H⁺ carrier

For any `x,y<N≤hPosition k b 0` and any binary symbol r,
`hNumericBinary K.binary k x y r =
 hNumericBinary L.binary k x y r`.

**Proof.** The literal generator for a true atom contains a real-real pair
`i<j, q,m≤k` and one of two orientations
`x=hPosition(k,i,q), y=hPosition(k,j,m)`
or the reverse. C34 applied to BOTH endpoints yields i,j<b. The
K=L old base column equality therefore transports the positive atom
in the SAME direction, proving K→L; swap K,L for the converse.
The negative atoms then follow by Boolean extensionality. Odd fake
vertices remain *L*-isolated on both sides.

For any old x<N and unary/diagonal symbol r,
`hNumericSingleton K.unary k x r =
 hNumericSingleton L.unary k x r`, likewise for diagonal.
If x has a genuine bounded-generation real representation,
its base index i is <b by C34 and the old unary/diagonal atom
agrees; if x is fake, both values are false.
The real representation is chosen by the SAME predicate
independent of K,L, so there is no noncanonical mismatch.

## C36: exact old complete L⁺ types stable under BASE plus numerical growth

At a physical old target `v<N` and an old socle cut `cut≤N`:

```
 (finiteNumericH K k N).partialTypeAt cut v
 =
 (finiteNumericH L k M).partialTypeAt cut v.
```

The old ordinary-L part is equal by C35 since all physical
coordinates used by the complete `PartialTypeWithE` record
are in [0,N). The auxiliary E table is **independent of the base
age-test model** and is clipped solely by its target, so equality
on all old E targets follows directly, even when the source is an
odd fake coordinate. This proves the complete directed L and E
atoms, unary/diagonal data and absent atoms, not just an age reduct.

The E free cut is also identical on both sides, by fixed-k
`finiteNumericHE` and the first-missing free-cut uniqueness theorem.
Taking cut to be the true old free level, the entire sigma-coded
raw original `rawTypeAtFree v` is E/L⁺-equal.

With actual avoided-family certificates `hAvoidKN` and
`hAvoidLM`, the two admissible Kpt ORIGINAL nodes of v
are literally equal, via subtype extensionality and proof
irrelevance—no artificial E added to an L-only B3 witness.

## C37: transport old seed Kpt prefixes and their complete closure

For U⊆Fin N, suppose the actual seed set X is represented by
the genuine original Kpt prefixes of A=finiteNumericH K k N:
`X⊆ambientPrefixPool family A hAvoidKN U`.

Then the very SAME X is represented in
`B=finiteNumericH L k M` via the physical address inclusion
`Fin.castLE : Fin N → Fin M`.
Proof: each old original Kpt node is literally equal to its
new-model counterpart by C36, so every old prefix z≤original
remains below the new original.

The true complete meet-and-selected-parameter closure
`closure (admissibleKptSTree family) I X` is formed in the
fixed forbidden-family Kpt tree, and hence it is the same Set
when viewed through either numerical model. Its real original
pool invariant in the new model follows from the already verified
`admissibleKpt_stage_closure_subset_pool`, with NO selected-shadow
projection.

Under the additional no competing (I2) meet at a fixed cut,
the same-closure physical-crossing theorem from Track E gives
the canonical full source+assigned upper L⁺ graph and corrected
B3 equality for the two models, even though K and L (and their
new original columns) may differ OUTSIDE the old b-block prefix.
An independent theorem may extract this next; do not smuggle
no-(I2) into the unconditional original/closure preservation result.

## Adversarial audit

1. **Both** base models K,L, and generation k, appear explicitly; changing k changes the numerical encoding and is NOT covered.
2. Distinguish b (base original block cutoff) and N (numerical coordinate cutoff). The crucial bound is N≤hPosition k b 0.
3. If old H⁺ N extends into base block b, an E/L⁺ type may see a newly chosen K-versus-L graph edge; the proposed result without N≤blockStart is FALSE.
4. Base binary agreement is required in BOTH ordered directions. A symmetric graph hypothesis is not silently supplied in the general signature theorem.
5. Base unary/diagonal agreement is separately required; old binary equality alone does NOT imply full L⁺ type equality.
6. The old base-model CARRIER predicates do not enter `finiteNumericHL` binary/unary/diagonal generation, so equality of the carrier fields is NOT postulated or inferred.
7. The source argument to E can be arbitrary even or odd; the finite E truncation is by target alone.
8. E column/free-level equality is exact for old target v<N, but for newly added E targets ≥N the small model may be false and the large model true.
9. Partial-type equality is only for `cut≤N`; a new socle index ≥N can reveal fresh E or L bits.
10. A real coordinate in the old numerical prefix may have different generation q; the positional argument uses *only* nonnegativity of q.
11. Fake odd coordinates have empty binary L but can appear as positive E sources; do not erase them.
12. The old seed X must be actual Kpt admissible nodes, not arbitrary raw partial types.
13. New base originals j≥b may carry arbitrary backward columns; verifying their prescribed K-free negative clique capacity is Track A/B's independent obligation.
14. Exact Kpt original equality uses true E-free cut, NOT the physical numeric coordinate v.
15. Two different finite avoidance witnesses belong to different source A_N / B_M structures, and equality of their proofs is not assumed.
16. Equality of actual closure X,I does not mean equality of envelopes for **different X or different I** (i.e., distinct diary occurrences); a full labelled cross-occurrence synchronisation is still missing.
17. This does not imply the unbounded recursive construction meets all its per-stage Henson left-density/age certificates, even though it proves old records persist **once** old base prefix agreement is established.
18. It supplies no uniform envelope cardinality bound, no eliminated K4 auxiliary microevents, no common source monoid orbit and no unconditional BRD characterisation.

## Lean targets, integration and status

New Track C module `Kk/NumericHBaseExtensionCoherence.lean` with strict, exact-head isolated module compilation and named standard-only axiom reports. Test at the EXACT source head and also run full-project build. Keep the PR draft/stacked until the gates pass; Track G alone handles `Kk.lean`, shared axioms registry and manuscript `kk.tex` / `validation.tex`.
