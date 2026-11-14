# Track C/E: actual full source and (B3) remain stable across **new base Henson original columns**

**14 November 2026. English-first proof and adversarial audit BEFORE Lean.** Independent new Track C branch from merged `lean-kk/main` `491dd99560b60d333ff778387f306b9a4ba6c8d9`. This uses the now MERGED nine-endpoint physical old-source base-extension result of PR #160, and differs from Track E's existing SAME-BASE run stability theorem.

## Physical input and missing step

The resolved-copy construction inserts NEW base Henson originals, not merely more numerical H+ coordinates of a fixed base graph. Let **K and L be different original base models** with the same directed binary/unary/diagonal signature. They agree on all **old** base original indices i,j<b in both tuple directions, and we fix the numerical generation k. Let the old physical numerical carrier end before the first new base block:

```
N ≤ hPosition k b 0,   N ≤ M .
```

These are the necessary cutoffs. All new base columns outside [0,b) may be different. Forbidden-family avoidance is required for both actual H+ finite models, not supplied by a fictitious expansion of an L-only age witness.

Let X be a fixed true Kpt seed set represented by original prefixes U⊆Fin N of `finiteNumericH K k N`. In particular, X is not an arbitrary marked-L selected-front approximation. Fix one selected level set I and put

`Z = closure (admissibleKptSTree family) I X`,

the exact complete meet-and-parameter closure.

### Theorem C41 — stability of OLD named source membership, including at I2

For any old finite original-name enumeration `original:Fin P→Fin N`, any v∈Fin P, and any cut p,

`closureSelectedOriginal family (finiteNumericH K k N) ... original Z p v`

holds iff the analogous statement with `finiteNumericH L k M` and names `Fin.castLE∘original` holds.

**Proof:** PR #160 proves that each old admissible Kpt original is *literally equal* to its original in the physically extended base model. The source predicate only says that some genuine z∈Z, strictly crossing p, lies below this Kpt original. Equality of original types transports the witness unchanged, in both directions. No no-(I2) hypothesis, no choice of an assigned upper successor type, and no comparison at fake vertices beyond the old carrier is needed.

### Theorem C42 — canonical full source/B3 stable on identical old Kpt closure, but different base K,L

Suppose the literal full meet-and-parameter closure Z has no SameComponent competing meet at p, including all auxiliary parameter nodes. Let F_K be `closureSelectedBoringData` in `finiteNumericH K k N` with **all** physical original names Fin N, and F_L its analogue in `finiteNumericH L k M` over Fin M. Then:

1. `F_K.source = F_L.source`: the COMPLETE dependent full L+ old types, including all unary/diagonal, directed L and auxiliary E, and all false bits;
2. for every T actually in this source, `F_K.target T = F_L.target T`: the COMPLETE assigned next full L+ type, not only its ordinary-L reduct;
3. `F_K.CorrectedB3 family ↔ F_L.CorrectedB3 family`.

**Proof:** The earlier verified real `admissibleKpt_stage_closure_subset_pool` certifies that every actual z∈Z lies below an old genuine Kpt original of K,N, despite meet/parameter generation. PR #160 transports the **same** X into a real original-prefix pool of L,M and the successor-tree stage closure theorem certifies an actual original witness there for every z∈Z. Thus both full physical original name universes are *exhaustive* for Z. The canonical physical old/upper full L+ relation of Z at p depends only on the Kpt node set Z, so the two physical relations are literally equal. Apply the existing independently verified Track E theorem `two_numericH_closures_B3_of_equal_full_crossing_relation` with `K₁=K, K₂=L, k₁=k₂=k, Z₁=Z₂=Z`, and the true no-(I2) hypothesis on Z. It gives precisely all three conclusions. Compare F.target only on F.source (the dummy total function outside source has no semantics).

### Theorem C43 — stability of TWO genuine AlgorithmRuns, changing the base model

Let R and S be arbitrary *actual* `AlgorithmRun (normalizedKptSMTree family) X top` with the SAME true complete Kpt seed X but potentially different chosen one-level monoid maps. The independently proved successor-tree `AlgorithmRun.I_eq` shows `R.I i = S.I i` at EVERY scanned level i≤top; this is **derived**, not assumed. Consequently, at EACH cut p<top where the actual pre-cut closure of R has no competing I2 meet, use C42 with `I = R.I(p+1)` and equality of the run-tail levels. The full old/next L+ prescribed source graph and corrected-B3 truth are therefore identical for the two physically different base models, for ALL such cuts.

This is a meaningful cross-original-extension theorem, not the same fixed-K carrier growth result already proved by Track E. It remains **same seed X**; a real new root modifies the seed set and may introduce extra events. The actual PR #165 new-root seed construction must be treated separately.

## Hostile review and nonclaims

1. **New base K may differ from L** on all new original columns; only old base i,j<b agreement is needed. For arbitrary different new columns the complete NEXT new-root source may differ; do not identify it with Z.
2. Both original binary directions are required; only positive adjacency or symmetry on the old prefix is insufficient in the general relational signature.
3. Unary and diagonal fields require separate old agreement; otherwise even an old Kpt source type may differ.
4. The numerical generation parameter k is FIXED; k→k+1 changes addresses and gating, and the theorem does not cover it.
5. The cutoff N≤hPosition k b 0 is essential. Without it old numeric coordinates can lie in the first changed base-original block and see newly changed L data.
6. Both models have genuine forbidden-family avoidance proofs; no artificial auxiliary E is assigned to an arbitrary L-only finite age witness.
7. PR #160's old Kpt original equality is at the TRUE E free level, not physical position v.
8. The real Z is the COMPLETE meet/parameter closure of X at I. Using only marked selected vertices is insufficient (K4 auxiliary cuts 10 and 22).
9. Named old-source membership C41 holds even when I2 forks: no single-valued target is assumed there.
10. F_K and F_L are compared at no-I2 cuts only; without this premise the physical crossing relation may not be functional and selecting different upper types is invalid.
11. The two full F.source sets are compared despite different numerical original pool cardinalities; exhaustiveness of the true complete closure is proved separately on both sides.
12. Equality of F.target is only asserted on actual F.source; outside source the prescribed total functions can choose unrelated dummy values.
13. `AlgorithmRun.I_eq` applies to actual runs with the EXACT same X/top/SMTree. It DOES NOT imply synchronization of distinct diary occurrences with different seed sets.
14. The physical E has odd fake positive predecessor bits; their membership in complete partial types is preserved. Fake numeric targets do not become real selected roots.
15. The new original columns must still be constructed with legitimate full old+gap K_(ell−1)-free neighbourhood certificates (Tracks A/B). Old-prefix equality does not produce those columns.
16. New root addition can create *additional genuine auxiliary I1/I2/I3 events*. This theorem only proves stability for the inherited fixed X / equal pre-cut I, not equality of new minimal resolved diary types.
17. No uniform bound on the full source index, no common fully labelled inverse monoid orbit and no unconditional KK BRD characterization follows.

## Validation contract

Create `Kk/NumericHBaseExtendedRunStability.lean` with exactly THREE named theorem endpoints, direct `lake build`, separate `lake env lean`/strict standard-only transitive axiom check, matching full-project CI. Keep central `Kk.lean`, shared registry and manuscript/validation markers untouched; coordinate later Track G integration.
