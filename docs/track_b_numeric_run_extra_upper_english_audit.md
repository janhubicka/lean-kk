# Track B — discharge the finite-pool premise in a genuine numerical-H AlgorithmRun
**13 November 2026: English proof, before Lean code.**

This is a strengthening of [the actual-I3 original-name audit](track_b_actual_i3_extra_upper_english_audit.md), Theorem D. The earlier theorem
`algorithmRun_nonstructural_I3_has_extra_upper_original` still takes as a hypothesis that *all* nodes in the pre-cut closure are prefixes of finitely many actual original names. In the numerical-H case this should be DERIVED from the real run, not silently postulated.

## Exact source and formula

Let `family` be an arbitrary finite list of normalized forbidden patterns in the fixed binary/unary/diagonal signature and `K` an age-test model with full carrier and avoiding that family. Set
`A=finiteNumericH K k N`, whose finite genuine carrier has size exactly N. Fix a finite seed-original pool `U : Finset (Fin N)`, a seed `X` contained in the genuine `ambientPrefixPool family A hAvoidA U`, and one actual `R : AlgorithmRun (normalizedKptSMTree family) X top`. Let `cut>0` lie below top, below N, and in `R.I 0`, with a top-height seed and no full-closure I1 or I2 event at that cut.

Define the **maintained final original names**
```
V = hStageOriginals K k N U (R.I 0),
original : Fin V.card → Fin N,
original j = (V.equivFin.symm j).1.
```

For the genuine source
```
Z = Envelope.closure (admissibleKptSTree family) (R.I (cut+1)) X
```
the pinned `numericH_algorithmRun_closure_original_in_final_pool` proves:
```
∀ z∈Z, ∃ v : Fin N, v∈V ∧ z ≤ A.kptOriginal family hAvoidA v.
```
Every `v∈V` has the **canonical** finite label `j=V.equivFin ⟨v,hv⟩`, and `original j=v`. Substitute into the preceding inequality to obtain exactly the finite-pool hypothesis of the merged Track B Theorem C, now without independent assumptions. Note that the selected levels used to define V are `R.I 0`, while the precise **source** of the B3 test is `R.I (cut+1)`; these are deliberately different.

Now take any marked-name predicate `Marked : Fin V.card → Prop` with one actual name w satisfying both `Marked w` and `cut+1≤A.freeLevel (original w).val`. Assume its true selected-stage B3 test passes. Apply the actual-run theorem to conclude:
```
∃ v : Fin V.card,
  closureSelectedOriginal family A hAvoidA original Z cut v
  ∧ cut+1≤A.freeLevel (original v).val
  ∧ ¬ (selectedStagePoolPrescribedData A cut original Marked)
       .PrescribedUpperLType
       ((A.partialTypeAt (cut+1) (original v).val).lReduct).
```
This is a real **numerical-H** finite-stage theorem; it does not require an assumed artificial common pool or a B3 failure hypothesis.

## Hostile checks

1. `hCarrier : ∀i, i∈K.carrier` is used to construct actual forbidden-family avoidance of `A.L`; arbitrary K need not have full carrier.
2. `hAvoidK` must be applied to the exact list `family`, not merely an existential clique-free condition when the list includes loop/asymmetric patterns.
3. `hX` is required to select genuine prefixes from U in A; without it the closure may be unrelated to A.
4. `cut<top` is needed by `numericH_algorithmRun_closure_original_in_final_pool`, including the `R.I (cut+1)` tail identity.
5. The final enumeration `Fin V.card` is allowed to be empty in principle; the marked w proves it is not empty in the application.
6. A closure node z may be a *proper prefix* of a maintained original. Do not assert z equals the full original.
7. Every original name is a `Fin N`, and `A.size=N` is an actual definitional property of finiteNumericH; no fake ambient-original address is inserted.
8. A selected `cut∈R.I 0` alone may be I1 or I2; both full closure structural exclusions are required for genuine I3 B3 failure.
9. The marked test must be the actual `selectedStagePoolPrescribedData` over the **same** maintained name universe; selected graph-age state F alone is not such a test.
10. The missing type conclusion is an ordinary complete **upper L-reduct** only. It does not assert equality/difference of auxiliary E source bits or upper-upper edges of arbitrary age-test W.
11. The theorem cannot be used to show all extra auxiliary types are determined by the macrodiary, or to prove a common labelled inverse-source orbit.
12. The fixed K4 cut-10 q2/x counterexample is compatible with, and motivates, this implication; it is not automatically a full instance of the abstract hypothesis without matching the actual run marked predicate.

**Verification gate:** one additional named theorem over the four proposed actual-run endpoints, for **413** exact standard-only reports if the baseline remains 408. Full hosted `lake build` and parser self-test required before merging or giving a global manuscript validation mark.
