# English proof and adversarial audit: arbitrary-subfront cover-or-equality via integer-witness lifting

**4 November 2026 — English FIRST, adversarial audit SECOND, Lean THIRD.**
This is the outstanding unrestricted *graph-age COVER macro-event restriction* assertion in the circulation manuscript. It is not the physical numerical-H graph gadget, not an Algorithm 5.4 full parameter-closed B3 comparison, and not a labelled inverse-source orbit theorem.

## 1. Relative genuine graph ages on an arbitrary selected subfront

Fix the actual finite ambient sort index set `Fin d`, forbidden clique bound `ell>0`, and any selected subfront `E : Finset (Fin d)`. A graph-age support is a nonempty finite support S of size at most `ell-1`. Only those S⊆E are visible on the subfront.

For the proof it is convenient to represent a relative age by a total function `H : IntegerGraphSupport d ell -> Nat`, with its values outside E **ignored**. Say H is a *relative integer-witness age on E* if:

1. for each eligible nonempty S⊆E, `1≤H(S)≤ell-1`;
2. for each such S, there is an actual normalized clique multiplicity vector `w : IntegerCliqueWeights d ell` supported ENTIRELY inside E (all coordinates outside E are zero), satisfying `sum_U(w)≤H(U)` for every eligible U⊆E and `sum_S(w)=H(S)`.

This is equivalent to the real integer-witness age on the chosen subfront, presented without reindexing E as a prefix. A genuine ambient integer age F restricts to a relative age: given its saturating witness at S, zero all coordinates outside E. The value on S stays unchanged, and all other restricted constraints only become easier.

## 2. English proof: lift ANY intermediate relative age into the full ambient age poset

Assume `lower ⋖ upper` is a genuine cover in the verified `IsIntegerGraphAge d ell` class. Fix any E and a relative integer age H on E satisfying

`lower(S)≤H(S)≤upper(S)` for every eligible S⊆E.

Define a raw bound on EVERY ambient support by

`B(S) = H(S) if S⊆E; otherwise B(S)=upper(S).`

Because lower≤H≤upper on E and lower≤upper globally, we have `lower≤B≤upper` pointwise. The actual finite integer-witness canonicalization `G=integerGraphAgeCanonical(d,ell,B)` is a genuine full graph age (using lower as a feasible admissible age), satisfying `lower≤G≤upper`.

**Claim: G(S)=H(S) for every S⊆E.**

The easy inequality is `G(S)≤B(S)=H(S)` from the canonicalizer's universal upper bound.

For the reverse inequality take a genuine *relative* H-witness w for S, supported on E, with `sum_S w=H(S)`. We show it respects **every** raw B-bound. For U⊆E it respects H(U)=B(U) by relative consistency. For U not contained in E, put `Q=U∩E`. Since w is zero outside E, `sum_U w=sum_Q w`. If Q is empty, this sum is zero and therefore ≤upper(U). If Q is nonempty, it is an eligible support and the relative H-consistency gives
`sum_Q w≤H(Q)≤upper(Q)≤upper(U)`, the last step being actual integer-witness age monotonicity for upper. Thus w respects B(U) for ALL ambient U. The canonical supremum includes w, so `H(S)=sum_S w≤G(S)`. Therefore `G|E=H`.

Since G is a genuine age with `lower≤G≤upper`, the genuine COVER axiom forces `G=lower` or `G=upper`. Restricting to E yields `H=lower|E` or `H=upper|E` on every visible support.

Combined with the fact that both ambient restrictions are relative ages, this says:

**A genuine cover of full finite integer-witness K_ell graph ages restricts on EVERY selected subfront E to either equality or a genuine relative-age cover.**

This includes arbitrary OVERLAPPING subfronts containing all of the distinguished cover support T; it is much stronger than PR #64's minimal-support omission theorem. No cover length, chosen changed support, or hMinimal hypothesis is required.

## 3. Adversarial audit

1. **Don't call H an ambient graph age.** It is only a genuine relative age on E. The mixed raw B is generally NOT a consistent age, which is why the actual integer-witness canonicalizer is indispensable.
2. **The witness must vanish outside E.** Otherwise the equality `sum_U w=sum_{U∩E}w` is false and the ambient F(U) bound may fail. We specify this property explicitly and prove restriction of a true ambient age supplies such witnesses.
3. **The empty intersection requires a separate case.** Supports are NONEMPTY; `U∩E=∅` cannot be used as a legal support and its bound H(∅) is undefined. The zero sum is bounded by upper(U) directly.
4. **Actual upper-age monotonicity is essential.** The inequality `upper(U∩E)≤upper(U)` must be derived from genuine integer weights, not pointwise lower≤upper.
5. **The lower ambient age supplies admissibility of G.** A raw bound B may have no admissible age below it in general; here lower≤B guarantees the canonicalizer itself is an age and a genuine intermediate.
6. **No strictness assumption hidden.** Even if upper|E=lower|E, the result is equality; if distinct, there are no proper intermediate relative ages, so it is a cover in the relative age class. This is the real intended dichotomy.
7. **E need not be an initial segment.** It is an arbitrary finite subset of Fin d. The proof uses supports S⊆E rather than a fictitious prefix labelling, avoiding an unproved canonical identification of active sort names.
8. **The values H outside E are irrelevant.** If H1 and H2 agree on all supports S⊆E they represent the SAME relative age; the theorem concludes equality only on those supports, not total function equality.
9. **No global numerical-H gadget.** This proves graph-age restriction of abstract actual canonical covers, not that the prescribed original reserved clique blocks cause exactly these changes in numerical H or that additional auxiliary I3 microevents are boring.
10. **No full corrected B3 transfer.** A finite relative age consistency witness is NOT an arbitrary upper L+ dependent continuation with E records. The genuine numerical-H K4 cut-10/cut-22 counterexample remains.
11. **No common labelled source or lower-bound proof.** The conclusion is algebraic locality of cover events across active subfronts, not an embedding into H+ or a proof of the big Ramsey upper/lower degrees.

## 4. Lean plan and validation contract

Define `IsRelativeIntegerGraphAge d ell E H` with actual full-normalized integer weights supported E. Prove ambient age → relative restriction. Define the mixed raw bound B by `if S.1⊆E then H(S) else upper(S)`. Prove lower≤B≤upper, full canonical G is an age between lower/upper, and the **exact E-restriction** identity `G(S)=H(S)` using the complete zero-supported relative witness. Finally prove no intermediate relative age, yielding the all-subfront cover-or-equality dichotomy. This should be kernel-checked with strict named transitive-axiom reports and NO new custom axioms/sorry.

**Manuscript discipline:** Retain protected BLACK text unchanged, add only olive explanations, green markers for genuinely proved Lean endpoints after successful CI, and TODOs if any step remains conditional.
