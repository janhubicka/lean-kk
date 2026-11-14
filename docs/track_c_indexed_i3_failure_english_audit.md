# Track C/D bridge: genuine AlgorithmRun I3 from absence of full indexed structural events

**14 November 2026 — English proof and hostile audit committed before Lean.**
Stacked behind Track C PRs [#128](https://github.com/janhubicka/lean-kk/pull/128), [#131](https://github.com/janhubicka/lean-kk/pull/131), [#133](https://github.com/janhubicka/lean-kk/pull/133). Their exact source requirements are not changed.

## C26: finite source certificate for an actual I3 cut

Fix a true finite numerical H+ `A=finiteNumericH K k N` with genuine base forbidden-family avoidance and full base carrier. Let U be a *finite* initial original-name pool, X a Kpt seed set with prefix representation over U, top a real AlgorithmRun scan height, and R its actual AlgorithmRun of height top. Require a seed in X at height top (the genuine top-root condition).

Let the ONE final full Kpt closure index be `params : Finset (AdmissibleKptNode family)`, with its literal `presentAt(cut,j)` mask for each actual pre-cut closure
`Zcut = closure (admissibleKptSTree family) (R.I(cut+1)) X`.
The index must cover the complete seed/meet/parameter closure, not the marked selected-front substructure.

Fix a POSITIVE cut p with `0<p<top`, `p<N`, which the **actual run** selected: `p∈R.I 0`. Assume exactly the following FINITE absence conditions:

(a) there is no active parameter index j with `lev(node j)=p`;

(b) there are no two active indices i,j strictly ABOVE p with identical full old `kptFullOldAtCut` and DISTINCT full upper `kptFullUpperAtCut` L+ records.

**Theorem:** the full corrected (B3) test FAILS for the actual choice of
`F = selectedStagePoolPrescribedData A p
    (hOriginalName (hStageOriginals K k N U (R.I 0)))
    (closureSelectedOriginal family A hAvoidA
       (hOriginalName (hStageOriginals ...)) Zcut p)`.

This is the genuine selected closure and the genuine final finite original-name pool. No arbitrary larger all-eligible pool or selected-shadow marked-only pool is substituted.

## English proof

The previous Track C structural classifier (PR #133) proves

`(I1(Zcut,p) ∨ I2Meet(Zcut,p)) ↔ (active-index-I1 ∨ active-index-full-fork)`.

The assumed finite absence of BOTH right alternatives therefore proves the literal *full-closure* no-(I1) and no-(I2) conditions (both, separately).

The pinned successor-tree theorem `numericH_algorithmRun_I3_stage_failedB3` already states: for any true numerical H+ AlgorithmRun at a positive selected cut, if the actual full pre-cut closure has no I1 and no I2, the canonical closure-selected prescribed F has **failed corrected (B3)**. Its proof uses genuine run interestingness and the full source/upper type graph, not any hand-chosen auxiliary E for a finite L-age witness.

Pass the two no-structural premises just derived into that theorem; the conclusion is exact.

**Contrapositive:** Under the same positive selected run hypotheses, if the canonical full F passes corrected B3, then the finite active source index MUST witness an I1-level node or a genuine full old-equal/upper-distinct fork. It does not say that F passes globally or that any particular microlevel is boring.

## Adversarial checks

1. The real `hTop : ∃x∈X, lev x=top` is NOT automatic for an arbitrary AlgorithmRun; keep it explicit.
2. The actual run-level selection `p∈R.I 0` is essential. The theorem does not classify unselected cuts.
3. The cut must satisfy `0<p<top` and `p<N`; no missing-zero or out-of-carrier assertion.
4. I1 and I2 are evaluated on the complete `R.I(p+1)` closure, including generated parameters and meets.
5. The finite source index covers final `R.I0` closure; its cut mask must be the actual pre-cut membership, not a shadow.
6. The fork compares the entire old+upper dependent L+ records, including auxiliary E and negative L atoms.
7. A trivial I1 self-meet does not yield a strict-crossing fork; the finite structural classifier has an explicit I1 disjunct.
8. The selected `F` is EXACTLY the pinned theorem's `closureSelectedOriginal` on the final maintained numeric pool; do not replace it by all Fin N.
9. This yields `¬F.CorrectedB3` in the genuine *L-only* age test; it does not invent an E relation on the arbitrary finite forbidden extension used by B3.
10. The contrapositive is only for selected cuts; outside R.I0 the conclusion may fail.
11. The actual K4 cuts 10 and 22 are mandatory hostile regressions and remain potentially interesting structural/auxiliary events.
12. No source index synchronization between different occurrences or common labelled monoid orbit is supplied.
13. No uniform bound on final pool size independently of ambient N or recursive age realization is supplied.
14. The main unbounded resolved-copy schedule still needs actual new-root and full L/E column construction and seed-pool preservation.
15. The theorem gives a finite diagnostic for I3, not a new unconditional finite BRD number.

## Acceptance

Formalize in `Kk/NumericHIndexedI3Failure.lean`, strict exact-head isolated module compilation with named standard-only axiom reports, plus full-project Lean gate. Do not modify the protected manuscript or shared central validation registry. Pass the precise theorem to Track D and E.
