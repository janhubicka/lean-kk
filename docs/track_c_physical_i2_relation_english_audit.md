# Track C/Track E bridge — exact physical I2 ⇔ nonfunctional full L+ crossing

**14 November 2026 — English proof and adversarial audit BEFORE Lean.**
Stacked on [Track C PR #128](https://github.com/janhubicka/lean-kk/pull/128), which has passed its exact-head isolated six-theorem axiom audit and independent full-project Lean workflow. Parent branch is not merged yet; no protected manuscript text is modified.

## The precise outstanding converse

Track E's existing `FullPhysicalClosureCrossing family Z cut` records *all* actual consecutive dependent Kpt ancestors as pairs of complete L+ types. Its existing `full_physical_crossing_nonfunctional_forces_I2` proves that two different upper types over the same old type force a genuine cut-level meet. The reverse was deliberately not asserted, because a trivial I1 meet at the tested level does not cross the cut.

The newly verified Track C PR #128 closes the missing mathematical distinction:
`¬I1(Z,cut) → (I2Meet(Z,cut) ↔ KptFullCutFork family Z cut)`.

We now connect the full-cut-fork *Option RawPartialTypeNode* data to Track E's actual full physical relation, WITHOUT choosing an original-name pool or an auxiliary E on a separate L-age witness.

## C20: every genuine Kpt crossing has exact physical old/upper data

Let z be an actual admissible Kpt node, cut<lev z, and z∈Z. Let the sigma-coded raw type of z be `z.val = (n,R)`, where R is its complete dependent L+ record at level n.

Define:
- `T = R.restrict(cut ≤ n)`, a complete `PartialTypeWithE cut db du dd`;
- `U = R.restrict(cut+1 ≤ n)`, a complete `PartialTypeWithE (cut+1) db du dd`.

Because the *actual* Kpt LevelTree ancestor is the literal induced full L+ restriction, the two equalities are exact:
`(⟨cut,T⟩ : RawPartialTypeNode db du dd) = (ancestor z cut).val`
and
`(⟨cut+1,U⟩ : RawPartialTypeNode db du dd) = (ancestor z (cut+1)).val`.

Consequently `(T,U)∈FullPhysicalClosureCrossing family Z cut`. Moreover the old and upper options from Track C #114 are exactly
`some ⟨cut,T⟩` and `some ⟨cut+1,U⟩`. No "source type" may be obtained by forgetting the auxiliary E-record or negative L atoms.

## C21: full Kpt fork ⇒ nonfunctional physical crossing

Suppose `KptFullCutFork family Z cut`, witnessed by a,b∈Z strictly above cut. Apply C20 to each: obtain (T_a,U_a) and (T_b,U_b) in the actual physical relation.

The fork says the old **Option RawPartialTypeNode** values are equal, so `⟨cut,T_a⟩=⟨cut,T_b⟩`; by sigma injectivity with a common first coordinate, `T_a=T_b`. The fork also says the complete upper options differ, so `U_a≠U_b`. Therefore the physical relation is genuinely nonfunctional: it has two distinct complete upper L+ types over the SAME old source T. This proof is independent of any no-(I1) assumption.

## C22: exact no-(I1) I2 ↔ physical nonfunctionality

Let `I2Meet(Z,cut)` mean the actual SameComponent meet at exactly cut. Assume there is **no actual Kpt node in Z of level cut**.

Then
```
I2Meet(Z,cut)
  ↔ KptFullCutFork family Z cut      (Track C #128)
  ↔ ∃ T U V, (T,U)∈FullPhysicalClosureCrossing Z cut,
               (T,V)∈FullPhysicalClosureCrossing Z cut, U≠V .
```

The second forward direction is C21, while the reverse comes from Track E's already verified `full_physical_crossing_nonfunctional_forces_I2` composed with the Track C no-I1 converse. This is a literal equivalence of actual mathematical obstructions, not a new assumed source-fidelity or selected-front hypothesis.

## C23: actual finite AlgorithmRun indexed event ↔ physical relation

For a genuine finite numerical H+ AlgorithmRun R and an EXACT complete final closure index `params` with `presentAt` masks, fix cut<top, use the actual pre-cut Z and assume no-(I1) there.

The Track C indexed full-fork theorem from PR #128 plus C22 identifies:
`∃ active i,j with same complete old L+ and distinct complete upper L+ ↔ physical relation nonfunctional at cut`.

All old/upper types are Kpt ancestors of literal nodes of this same run, not selected-original shadows or different actual-closure families.

## Hostile checks

1. No-I1 is mathematically necessary: a sole z∈Z at lev z=cut yields a trivial cut-level meet but no crossing old/upper pair.
2. In `RawPartialTypeNode db du dd = Σ n, PartialTypeWithE n db du dd`, the cutoff proof must use the *exact* dependent `restrict`, not an untyped tuple.
3. Verify BOTH cut and cut+1 ancestors with the actual Kpt `admissibleKpt_levelTree_ancestor_eq` theorem.
4. The two physical upper types must actually be DISTINCT; different Kpt nodes with identical upper restrictions are no fork.
5. Comparing `Option RawPartialTypeNode` records requires sigma injectivity to recover equality of the dependent `PartialTypeWithE` values.
6. No extra E relation may be assigned to an arbitrary finite corrected-(B3) L-only witness; all E lives in the actual physical Kpt nodes.
7. The source is complete even when odd fake numerical coordinates occur as E-predecessors of an H-real target.
8. The full physical relation is meaningful even at I2; we do NOT assume it is the graph of any single-valued prescribed F at those cuts.
9. Finite active-index statements require the actual `presentAt` mask for `R.I(cut+1)`, not the final closure mask alone.
10. SameComponent is only inferred from an actual old Kpt ancestor; no meet of disjoint forest components is used.
11. The result does not identify arbitrary Kpt source names between different H+ presentations or produce an event-order synchronization.
12. It does not classify I3 or corrected B3 without the separate selected-target/failure analysis.
13. The K4 microcuts 10/22 remain potentially interesting; a selected-shadow equality is insufficient.
14. No uniform bound on final maintained high-generation pool names is proved here.
15. The recursive multi-root numerical H+ resolved schedule still needs independent full L/E source realization.
16. The common labelled inverse-source orbit and big Ramsey degree characterization remain open.

## Proof/validation procedure

Put the physical converse and optional indexed corollary in `Kk/NumericHPhysicalI2Fork.lean` with direct module compilation, exact named standard-only transitive-axiom reports and full-workflow build. Do not alter central shared files or manuscript protected text; pass the exact interfaces to Track D/E after the gates pass.
