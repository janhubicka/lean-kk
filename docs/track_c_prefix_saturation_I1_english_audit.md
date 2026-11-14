# Track C adversarial obstruction: seeding a Kpt *prefix pool* forces every level I1

**14 November 2026 — rigorous English counterexample, hostile audit BEFORE Lean.**

## Mathematical issue in the first PR #165 candidate

The original proposed seed family was
`Y_bad = closure I X ∪ ambientPrefixPool family B hAvoid W`,
where W includes a physical Kpt original w with true free level top.

**This is not a bounded resolved seed construction**, regardless of how good the numerical Henson one-point L columns may be. It forces ALL scanned levels 0,...,top to be selected by the actual Algorithm 5.4, solely via I1. The corrected PR #165 candidate uses only the genuine new original Kpt nodes as seeds, not all their proper prefixes. This document formally certifies why the repair matters.

## Lemma N1 — saturation of any Kpt predecessor set

Let T=AdmissibleKptNode family with its verified forest LevelTree, let `x:T` satisfy `lev x=top`. Let the actual seed set `Y:Set T` contain **every ancestor of x**, i.e. `∀z≤x,z∈Y`. Let R be an actual
`AlgorithmRun (normalizedKptSMTree family) Y top`.

Then

```
∀ p:Nat, p≤top → p∈R.I 0.
```

**Proof.** Fix p≤top. The verified Kpt LevelTree gives the unique ancestor `a_p=ancestor(x,p)` with `a_p≤x` and `lev a_p=p`. Prefix saturation places a_p in Y, hence also in the ACTUAL pre-cut closure `closure (admissibleKptSTree family) (R.I(p+1)) Y`, by `Envelope.subset_closure`.

For p<top, this is a literal Algorithm 5.4 I1 witness at cut p. Thus `R.interesting_step p ...` selects p in `R.I p`; the checked run-tail identity `R.I_eq_final_tail_of_run p` puts p in `R.I 0`.

For p=top, the initial run condition `R.topI = {top}` gives top∈R.I top, and the same run-tail identity gives top∈R.I0. There is NO appeal to corrected B3, no no-I2 hypothesis and no arbitrary constructor choice.

Since no level >top can be selected by `R.I_mem_bounds`, the final selected level set is exactly `{p | p≤top}`. In particular its cardinality grows with top; it cannot be bounded by the number of selected graph vertices independently of the numerical cut.

## Lemma N2 — the genuine physical ambientPrefixPool is saturated

Let B be any REAL finite enumerated partial structure avoiding family, and w:Fin B.size be an actual original with `B.freeLevel(w)=top`. If the Kpt seed set Y contains `ambientPrefixPool family B hAvoid W` for any W containing w, then it contains **every** predecessor of the actual original `B.kptOriginal family hAvoid w`. By its verified Kpt original level, `lev(B.kptOriginal w)=top`; invoke N1 to conclude every p≤top selected.

There is no special numerical H assumption beyond genuine physical Kpt admissibility. In particular the obstruction holds even for the **all-old-closure plus full new-root prefix-pool** Y_bad of PR #165. Its unsuitability is mathematical, not a Lean elaborator artifact.

## Hostile checks

1. Do NOT confuse `ambientPrefixPool` (a COVER/representation) with the seed set of the envelope algorithm.
2. The proof uses the actual Kpt LevelTree with *admissible* ancestors, not arbitrary raw truncated L tables.
3. All predecessors have levels p≤top exactly, including p=0 (root type).
4. I1 is checked on the actual pre-cut closure, not selected-front L shadows.
5. The no-(I2) and corrected-(B3) tests are irrelevant because I1 already fires.
6. `R.I p` and `R.I 0` are not conflated; use the proved run-tail theorem to transport membership.
7. At p=top use `R.topI`; `R.interesting_step` only applies for p<top.
8. The statement is independent of how the AlgorithmRun chooses one-level monoid maps.
9. The physical original's Kpt level is its E-free level, not its numerical index.
10. Odd fake E predecessor bits remain in the actual full Kpt prefixes; no fake vertex is made a new REAL root.
11. If Y contains *only the original x* rather than all its proper prefixes, no all-level I1 conclusion follows from this argument.
12. Inherited old meet/parameter-closure seed nodes can still create their own genuine auxiliary events. The corrected construction removes only automatic NEW-root prefix saturation.
13. The finite source-index theorem for Y_bad may be perfectly true and kernel-clean; it does not certify a bounded minimal envelope.
14. This negative result does not assert anything about cross-occurrence orbit or exact BRD degrees.

## Lean/CI acceptance

New Track C module `Kk/PrefixSaturationI1Obstruction.lean` with three direct standard-only theorem endpoints. Isolated exact-head `lake build`, strict named transitive-axiom parser, and separate full-project Lean workflow. Do not alter manuscript black/olive prose, validation marks or shared registry. Pass the precise obstruction to Track B, Track D and Track G for avoiding future overgeneration errors.
