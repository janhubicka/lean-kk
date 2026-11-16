# Track D — ordinary old L-bit certificates exclude FULL dependent-L+ I2 forks
16 November 2026. English proof and adversarial audit BEFORE Lean.

## Scope, background and the actual missing bridge

The verified Track D generation-zero separator [PR #264](https://github.com/janhubicka/lean-kk/pull/264) shows an actual older original v_0, before a specified physical numerical-H cut, can distinguish the COMPLETE OLD dependent L+ source types of a selected TOP physical original and a later negative auxiliary original. That is a rigorous pairwise statement about genuine physical original names (and does not magically put those names into the complete active Kpt closure).

To rule out the full structural I2 of one actual AlgorithmRun, one must test ALL potential pairs of the ENTIRE full closure, including generated meet and parameter nodes. This cannot be inferred from the selected-vs-negative-aux pair alone. The already merged
`Kk/NumericHI2FullFork.lean` proves, under no-(I1),
  I2 ↔ ∃ active full Kpt nodes a,b crossing c with
           equal COMPLETE old dependent L+ records
           and UNEQUAL COMPLETE next dependent L+ records.

The also merged
`Kk/NumericHExhaustiveRunIndex.lean` constructs a finite index `params` of the TRUE final Kpt closure `closure(R.I 0,X)` with per-cut Boolean live masks of the distinct TRUE pre-cut closure `closure(R.I(c+1),X)`.
`finiteNumericH_run_no_I1_I2_iff_indexed_full_fork` gives the EXACT index version of I2, again assuming no I1. These are checked sources; no selected graph-age projection or arbitrary source restriction is used here.

## Concrete certificate

For `family : List (NormalizedForbidden 1 0 1)`, nodes a,b : `AdmissibleKptNode family`, and cut c, define `KptOldOrdinaryBitSeparation family a b c` to mean that there exist COMPLETE dependent OLD type records `T,U : PartialTypeWithE c 1 0 1`, and one concrete old coordinate `q : Fin c`, such that

  kptFullOldAtCut a c = some (⟨c,T⟩ : RawPartialTypeNode 1 0 1),
  kptFullOldAtCut b c = some (⟨c,U⟩ : RawPartialTypeNode 1 0 1),
  T.lReduct.binary (some q) none 0
      ≠ U.lReduct.binary (some q) none 0.

This is an explicit old ordinary-L bit, not a fabricated E property. Both old complete L+ records are extracted from genuine Kpt nodes. The certificate is only available when both Kpt nodes genuinely cross the cut, as the nonempty old-record equation explicitly demands.

**First theorem:** this certificate forces
`kptFullOldAtCut a c ≠ kptFullOldAtCut b c`.
Proof: equality of those optional raw values plus the two `some (⟨c,...⟩)` facts forces T=U by constructor injectivity; the differing old ordinary bit contradicts T=U. The proof does not discard auxiliary E atoms; their full record inequality is already witnessed in the ordinary reduct.

**Second theorem:** for any genuine full closure Z at cut c without I1, if EVERY actual active pair a,b strictly crossing c with unequal full next-dependent-L+ records has such an old ordinary bit certificate, then there is NO competing I2 meet at c. Proof: suppose I2; use the already verified I2↔full-fork theorem to obtain one genuine a,b with SAME complete old records but different next records. Apply the universal ordinary-bit certificate to that SAME a,b; its first theorem makes the full old records unequal, contradiction.

**Third theorem (ACTUAL finite index):** for one genuine finite numerical-H AlgorithmRun, let `params` be any exact exhaustive final Kpt source index and `presentAt` its actual pre-cut live mask (the ordinary verified Track C hypotheses). Assume no I1 at a positive cut below top. Suppose every two ACTIVE and strictly crossing indexed nodes with different upper FULL raw L+ records have a `KptOldOrdinaryBitSeparation` witness. Then no full I2 occurs at this cut. Proof via the checked exact index I2↔two-index-fork theorem and the first ordinary-bit inequality.

This is a stronger, physically meaningful sufficient certificate rather than simply restating equal-old⇒equal-upper: it requires a CONCRETE OLD ordinary L coordinate whenever upper records differ. In the concrete resolved Q application, generation-zero copies of actual OLD Q neighbours supply these bits in the selected-positive vs negative-auxiliary case. Other active parameter/meet pairs still need separate checks.

## Adversarial checks (19)

1. Do not confuse the final `params` domain (from `R.I 0`) with per-cut active `Z_c=closure(R.I(c+1),X)` (from `presentAt c`).
2. An indexed Kpt node can be a meet/parameter, not a physical original of the selected diary. The certificate quantifies over ALL indexed active crossing nodes.
3. No I1 is a genuine necessary premise for the I2↔full-fork equivalence; a trivial self-meet at an I1 endpoint is not a pair of strictly crossing upper types.
4. The old full L+ record is an `Option (RawPartialTypeNode 1 0 1)`; it may be `none` for a non-crossing node. The explicit `some (⟨c,T⟩)` equations prevent false use of the bit witness on a node ending at c.
5. The specific bit coordinate q lies in `Fin c` and is evaluated as a directed OLD-to-future binary atom `(some q,none)`. Do not substitute a future-future atom or an auxiliary E bit.
6. The raw dependent old type is `PartialTypeWithE c 1 0 1`. Equality of some Sigma values implies equality of their full type records; comparing ordinary projections cannot fail to distinguish an already equal full record.
7. A different old ordinary bit is sufficient to show full dependent L+ types are unequal, but absence of such a bit does NOT show equality (auxiliary E, unary/diagonal, and negative relations may still distinguish). This is only a SUFFICIENT I2 exclusion.
8. The successor-tree I2 definition considers ANY same-component meet, including trivial meet at I1; never claim no I2 from ordinary bits alone without no I1.
9. Do not require no I2 to construct the full source index; the checked uniform exhaustive index is valid even when the physical crossing relation is nonfunctional.
10. The `presentAt` Boolean mask must be exact for all cuts; do not replace it by membership in the final pool or selected graph front.
11. The two-index condition requires BOTH nodes cross strictly above c; no mere active presence suffices.
12. Negative atoms are preserved in complete old L+ records; the witness tests one concrete bit but does not infer all bits or E.
13. No relative graph-age monotonicity/capacity loss is claimed from a Kpt bit distinction.
14. A selected-vs-negative-aux pair is only one of potentially many indexed pairs; this theorem states exactly the additional universal pair coverage that still needs proof from the Q schedule.
15. The physical generation-zero separator already checked in PR #264 supplies the bit for physical originals with strict base-order/edge hypotheses. It does not supply it for arbitrary generated meet nodes.
16. No asserted correspondence of two different copies of the same diary or their labelled inverse source is used.
17. The full small-independent (n≤3) upper BRD and common source remain PENDING.
18. Keep frozen manuscript black prose untouched, and use a small olive TODO for eventual application pairing; no validation mark until the new exact-head CI passes.
19. Compile the exact generic and true-run forms in Lean and audit every qualified theorem with the strict standard-only axiom parser. A successful general Lean workflow that fails to import this new module is insufficient, as demonstrated by failed earlier PR #263.

## Implementation

New `Kk/FullKptOldLBitNoFork.lean` imports `Kk/NumericHStructuralCutClassifier.lean` and `Kk/NumericHI2FullFork.lean`. Define `KptOldOrdinaryBitSeparation` explicitly. Prove:
- `kpt_old_ordinary_bit_separation_forces_full_old_distinct`
- `kpt_no_I2_of_all_upper_mismatches_have_old_L_bit`
- `finiteNumericH_run_no_I2_of_indexed_old_L_bit_separators`.

The final source has a dedicated exact-head module build and strict three-name transitive-axiom audit. No `sorry`, custom axiom or `admit`. All proof scope and barriers above must remain written explicitly.

**Proof-driven next task**: for each omitted cut of the resolved independent-set Q source, supply the complete finite Kpt closure indexed pairs and find a generation-zero Q old separator (or another old L bit) for every pair with unequal next full L+. The verified K4 singleton old-neighbour extractor (PR #263 once repaired) is relevant for some such pairs but not all.
