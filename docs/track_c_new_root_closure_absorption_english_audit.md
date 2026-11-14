# Track C — absorb the inherited old closure in a genuinely selected new-root pre-cut

**14 November 2026. English mathematical proof and 18 adversarial checks BEFORE Lean.**
Branch from merged main `600372b52f017bc753e0285c2593747b8b473b8b`, which includes the repaired original-only new-root Kpt seed definition from PR #165, genuine chronological bound PR #185, and the independent I1 original-only regression PR #187. We do not modify the protected manuscript or global validation markers.

## The actual remaining question

The corrected PR #165 constructs the next initial seed set as

```
Y = closure (admissibleKptSTree family) I X
      ∪ ((w ↦ B.kptOriginal family hAvoid w) '' W)
```

in the true physical expanded `B=finiteNumericH L k M`. This correctly avoids pre-inserting all proper ancestors of NEW roots as initial seeds (the old all-prefix formula would force every level to be I1, independently of B3).

But there is still a possible source of overgeneration: the entire **old meet-and-parameter closure** `closure_I(X)` is inserted as initial seeds. At a cut p of the new AlgorithmRun R, the genuine pre-cut closure is

`closure_{R.I(p+1)}(Y)`.

Could the preinserted old closure artificially force an I1/I2 event not generated from the original seeds X and the actual NEW original Kpt nodes? This needs to be answered at the **true** pre-cut set, not the initial Y or the selected graph-age shadow.

## C47 — abstract closure absorption theorem (no H-specific assumptions)

Let S be ANY genuine successor tree on a LevelTree T. For seed sets X,O⊆T and selected level sets I,J⊆Nat, assume `I⊆J`.

Then

```
closure S J ((closure S I X) ∪ O)
  = closure S J (X ∪ O).
```

**Proof, first inclusion.** Put C=`closure S J (X∪O)`. It is verified to be meet-closed and J-parameter-closed by `closure_meetClosed` and `closure_parameterClosed`. Since I⊆J it is also I-parameter-closed by `ParameterClosedOver.mono_levels`. Since X⊆X∪O⊆C, closure minimality implies `closure S I X⊆C`. Also O⊆C. Consequently `closure S I X∪O⊆C`, and the minimality of the J-closure yields the desired inclusion.

**Proof, reverse inclusion.** X⊆`closure S I X` by `subset_closure`, so X∪O⊆`closure S I X∪O`. This union is contained in its own J-closure. Applying the same closure minimality (and J-meet/parameter-closure) gives `closure_J(X∪O)⊆closure_J(closure_I X ∪O)`. No unproved distributivity of closure over union is assumed.

The **hypothesis I⊆J is essential**. If an old selected level i∈I is absent from J, old closure may have generated a parameter at a lower level which the new J-closure of X∪O cannot generate. The theorem does NOT assert equality for arbitrary unrelated I,J.

## C48 — EXACT physical repaired new-root closure absorption

Set `O=(fun w:Fin M => B.kptOriginal family hAvoid w) '' W`. The repaired `finiteNumericH_physicalExtendedSeeds` is literally `closure_I X∪O`. Thus for ANY `J⊇I` the complete **actual Kpt** meet-and-parameter closures agree:

```
closure_J(finiteNumericH_physicalExtendedSeeds family B I X W)
  = closure_J(X ∪ O).
```

This uses the COMPLETE dependent-L+ Kpt successor tree, not graph adjacency alone and not a selected-front approximation. It applies to multiple real new roots, including roots with different actual free cuts. It does not assert these resulting closures are finite without the separate physical original-pool bounds.

## C49 — real AlgorithmRun pre-cut I1/I2 and physical L+ crossing data

Let `R` be an ACTUAL `AlgorithmRun (normalizedKptSMTree family) Y top`, where Y is exactly the repaired physical new-root seed set above. Fix a tested `cut<top` and suppose the old selected levels are retained among the new **higher** selected levels:

`I⊆R.I(cut+1)`.

Then, putting J=`R.I(cut+1)`, C48 shows that the actual pre-cut closure of the corrected Y is EXACTLY the pre-cut closure obtained from the **bare old original seeds X and new original nodes O**. Consequently:

1. The genuine I1 predicate (actual level-cut Kpt nodes) agrees in both closures.
2. The genuine I2 competing-meet predicate agrees in both closures, including trivial I1 self-meets.
3. Their entire canonical `FullPhysicalClosureCrossing family _ cut` relations agree *literally*. All old and upper complete L+ records, auxiliary E, fake E predecessors and negative L atoms remain in the same relation.

The conclusion is unconditional in the cut's I1/I2/B3 status; it does NOT require no-(I2). It does not choose a nonfunctional F at an I2 fork. When no-I2 holds, the existing verified full source-graph theorem may be applied to this exact same closure.

**This is stronger than the positive seed-only regression PR #187:** there we knew the corrected new-root component did not add *initial* lower I1 seeds; here, whenever I⊆new higher-selected J, the ENTIRE **generated pre-cut closure** and all its physical event data coincide with the minimal seed family X∪O.

## C50 — derive the crucial level-set inclusion from actual run-tail data

At a real cut p<top, assume:

- every old selected level q∈I remains selected by the new run, `I⊆R.I0`;
- every q∈I is strictly **above** cut, `∀q∈I, p<q`.

The checked `R.I_eq_final_tail_of_run (p+1)` yields
`R.I(p+1)={q∈R.I0 | p+1≤q}`.
Thus both conditions give `I⊆R.I(p+1)` and C49 applies. No independent hIJ proof need be assumed.

This is the precise **retention obligation** needed to eliminate old-closure pre-seeding from actual source analysis. The theorem does not magically prove old I levels survive addition of new root seeds. That is a separate, genuinely nontrivial monotonicity/diary-stability problem: I1/I2 witnesses persist when seed sets grow at a FIXED level set, but I3 corrected-B3 failures need not be monotone under extra source constraints. Never silently infer `I⊆R.I0`.

## Hostile checks

1. This is true closure under REAL componentwise Kpt meet and selected successor PARAMETERS, not arbitrary graph-theoretic downward closure.
2. The closure operator need not distribute over union; the proof uses least closed supersets and the level inclusion `I⊆J`.
3. Do NOT drop `I⊆J`, especially when the old selected level generating a parameter is absent from the new run's higher selected levels.
4. The result compares the SAME real Kpt original nodes X and O, not two independently labelled model expansions.
5. It uses the repaired original-only seed definition; the superseded all-prefix Y would still trivially force every I1 level and is not covered by the intended reduction.
6. The physical source set O is an image of ACTUAL admissible Kpt originals with generated E, not their full prefix pools.
7. The exact I1 and I2 predicates compare their complete TRUE closure nodes; no replacement by a selected L-only age.
8. Even at I2 cuts, the **relation** `FullPhysicalClosureCrossing` is meaningful; do not assert it is a function there.
9. The first absorption inclusion requires J-param-closed ⇒ I-param-closed; do not confuse reverse direction.
10. The second inclusion requires `X⊆closure_I X`, not an assumption that X itself is closed.
11. A new actual root may spawn additional meets with old sources or genuine selected parameters. Those events remain present on BOTH sides; the theorem does not eliminate them.
12. The theorem makes no claim that every cut has old I⊆R.I(cut+1); it states the exact condition needed.
13. The retained-old-level condition `I⊆R.I0` is not a consequence of two AlgorithmRuns having the SAME seed set, because these runs have different seeds.
14. The chronological tight-cutoff theorem controls node levels, not retention of interesting levels.
15. This removes redundant old closure generation at particular pre-cuts, but not necessarily in an arbitrary global new-root AlgorithmRun.
16. We still need the actual new Henson original backwards K_(ell-1)-safe columns from Track A/B and the exact canonical resolved macrodiary sequencing.
17. K4 auxiliary microcuts 10/22 remain possible genuine I1/I2/I3 events; no false boring-level conclusion is made.
18. No cross-occurrence labelled source monoid inverse orbit, uniform degree bound or unconditional BRD result is inferred.

## Lean/CI

New module `Kk/NumericHNewRootClosureAbsorption.lean` with four exact theorem endpoints: general closure absorption, physical repaired-root specialization, actual-run pre-cut I1/I2/full physical relation equality, and run-tail derived absorption. English committed before Lean. Require exact-head direct `lake build`, strict four named standard-only transitive axiom reports, and independent normal full-project Lean workflow. Do not alter central registry/import aggregator, protected manuscript or validation marks.
