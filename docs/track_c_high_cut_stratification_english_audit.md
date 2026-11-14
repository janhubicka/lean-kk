# Track C — exact high-cut closure stratification for ALL actual new-root cuts

**14 November 2026. English-first proof + adversarial audit BEFORE Lean.**
Stacked behind Track C PRs #192 (4 exact verified closure absorption endpoints), #194 (genuine AlgorithmRun seed monotonicity) and #196 (increasing-height retention with a real old top seed). No central/black manuscript edits.

## A stronger theorem than whole-closure absorption

The exact preceding theorem said
`closure_J(closure_I X ∪ O)=closure_J(X∪O)` if *ALL* old selected levels `I⊆J`.
For actual AlgorithmRun pre-cut J=R_new.I(p+1), old selected levels q≤p are intentionally absent from J. Thus the strong equality need not hold and its direct use only covered cuts strictly below ALL old selected levels (often vacuous if 0 is selected).

**However, the actual I1/I2 and complete old/upper L⁺ crossing relation at cut p depend only on Kpt nodes with level AT LEAST p.** Parameter creation at a level i≤p produces parameters of level **strictly less than i**, so below p. Meets cannot increase levels. Thus old selected levels at or below p cannot create additional cut-p witnesses or p-crossing nodes.

### H1 — closure stratification under selected-level inclusion only ABOVE the cut

Let S be any actual successor tree over T with `LevelTree`, X,O⊆T and old/new selected levels I,J⊆Nat. Fix a cut p. Assume

```
∀ i∈I,  p<i → i∈J .
```

Write
`Cold=closure S I X`,
`C=closure S J (X∪O)`,
`Z=closure S J (Cold∪O)`,
and `Low_p={z:T | lev z<p}`.

**Claim:** For EVERY `z:T` with p≤lev z,

```
z∈Z  ↔  z∈C .
```

**English proof via a genuine closure invariant (no false distributivity).**

Define `D=C∪Low_p`. We prove it is closed under both meet and parameter generation over every level in I or J.

- **Meet closure.** If both actual componentwise-meet inputs are in C, their meet lies in C by the verified closure_meetClosed. If either input has level <p, the meet is below that input by the verified `meet_le_left/right`; hence its level is also <p, so the meet lies in Low_p. The forest-component condition is essential.
- **Parameter closure.** Let a∈D have an actual successor at selected base level i and a parameter z of its successor list. The verified STree `parameter_level_lt` theorem gives `lev(z)<i`. If i≤p, then lev(z)<p and z∈Low_p, regardless of a. If i>p and i belongs to the old level set I, the hypothesis makes i∈J. If it is an already chosen new level i∈J, that is automatic. For i>p, a CANNOT lie in Low_p because its true successor base i satisfies i<lev a; therefore a∈C, and the verified J-parameter closure of C yields z∈C. No other kind of new node is introduced.
- **Cover old closure.** X⊆C because X⊆X∪O, and D is I-closed by the preceding argument, hence the least-closure theorem gives `Cold⊆D`. Also O⊆C⊆D, so Cold∪O⊆D.
- **Cover the actual NEW closure.** D is also J-closed. By least-closure, `Z=closure_J(Cold∪O)⊆D`. At node z of level ≥p the Low_p alternative is impossible, so z∈C.
- **Reverse inclusion.** `X⊆Cold` by subset_closure, so `X∪O⊆Cold∪O`. Monotonicity of genuine closure in seeds yields `C⊆Z`, without any hypothesis on I,J.

This proves the desired EXACT membership equivalence above the tested cut p. It does NOT claim Z=C below p; old low selected parameter nodes can genuinely differ there.

### H2 — cut-p I1/I2 and COMPLETE physical L⁺ relation depend only on nodes of level ≥p

For any two actual Kpt node sets Z,C satisfying the above-cut membership equivalence at p:

1. **I1:** a witness z with lev z=p is in Z iff in C.
2. **I2:** a competing same-component meet of level p has both endpoints at levels ≥p, since meet≤both. Thus exactly the same pairs witness I2 in Z and C.
3. **FullPhysicalClosureCrossing:** every physical crossing is witnessed by a single Kpt node of level **strictly >p** with exact dependent old/upper L⁺ ancestors. Since its membership is the same, the ENTIRE nonfunctional physical crossing relation is identical. All E, fake predecessor, unary/diagonal, negative L data are literally unchanged. No chosen F target is compared at an I2 fork.

No no-(I2) premise occurs in these three statements.

### H3 — repaired new-root pre-cut event equality when only OLD HIGHER levels survive

Let B be the actual finite numerical H+ model, O the set of genuine newly inserted physical Kpt originals, and
`Y=closure_I(X)∪O` the corrected PR #165 stage. Let Rnew be an actual AlgorithmRun on Y at top T, and fix p<T. Assume **only**

```
∀i∈I, p<i → i∈Rnew.I(p+1).
```

H1 yields equality of genuine physical closure membership AT/ABOVE p for the run's true pre-cut closure `Z=closure_{Rnew.I(p+1)}Y` and the bare-original pre-cut closure `C=closure_{Rnew.I(p+1)}(X∪O)`. H2 yields EXACT I1, I2, and full physical crossing-relation equality, including auxiliary microevents.

This is **strictly stronger** than PR #192's literal whole-closure equality requiring all I⊆J.

### H4 — obtain HIGHER-level retention at EVERY cut from cross-height seed monotonicity

Suppose I is the exact selected level set of a genuine old AlgorithmRun Rold at oldTop t, with a genuine top-level seed, and Rnew is a genuine run on repaired Y at newTop T≥t. The preceding cross-height selected-level monotonicity theorem (PR #196) proves `Rold.I0⊆Rnew.I0`.

For each p<T and each q∈I=Rold.I0 with p<q, the verified run-tail identity for Rnew gives q∈Rnew.I(p+1). Hence the hypothesis of H3 holds **at EVERY tested cut p**, with NO “p below all old levels” guard.

Consequently, for every new scan cut p<T the entire actual pre-cut **I1/I2/full physical old+upper L⁺ relation** of corrected Y agrees with the bare old original X plus genuine new originals O. This completely removes the spurious inherited-closure overgeneration concern at the level of cutwise structural events, PROVIDED the old top seed and genuine cross-height run hypotheses hold.

**This DOES NOT assert boringness, identical macrodiaries for different rooted occurrences, or a bounded number of new I3 events. It says that inherited old-closure preinsertion does NOT itself alter any new-run structural cut record; actual interaction with the new original Kpt nodes is fully retained and may create new events.**

## Adversarial checks

1. High-cut threshold is **p≤lev z** for I1 and meet endpoints, while physical crossing witnesses require **p<lev z**. Do not confuse.
2. The hypothesis is only `∀i∈I, p<i→i∈J`; old levels i≤p may be missing from J. Whole-closure equality is generally false in that case.
3. Selected parameters have **strictly lower level than their base i**, by the actual STree `parameter_level_lt` theorem. Without strictness the proof fails at i=p.
4. Same-component meets cannot increase levels. Do not use arbitrary total meet across unrelated forest components without SameComponent.
5. The union invariant `C∪Low_p` must be proved meet-closed and parameter-closed for BOTH I and J; no handwaved closure distributivity.
6. A parameter generated from an input already below p cannot have base level ≥p because its base is strictly below its source's level.
7. All old initial X nodes lie in C by actual `subset_closure`; the new original seed O lies in C as well.
8. The full closure `Z` may have additional nodes below p, and the theorem does NOT erase those. Lower parameters may matter at later lower cuts.
9. I2 meet at level p requires actual SameComponent witnesses; their levels≥p must be derived from meet≤both.
10. Physical source relation is *choice-free* and valid at I2 forks. Do not incorrectly identify arbitrary assigned F.target at a nonfunctional cut.
11. All L+ atoms including negative E/L, fake odd E predecessors, unary and diagonal are preserved because actual Kpt witness nodes are literally the same.
12. This is a theorem on actual Kpt successor trees, not a graph selected-front approximation.
13. Genuine AlgorithmRun higher selected level sets are **run tails**, not every old level; use `R.I_eq_final_tail_of_run` correctly.
14. The monotone selected-level comparison across different scan heights requires a GENUINE old top seed (or same height). Do not silently assume it.
15. A different Kpt seed set not containing old X need not retain old selected levels; no cross-occurrence orbit claim.
16. The corrected stage seeds actual NEW Kpt originals, not all their ancestor prefixes (which would force every I1 level).
17. The theorem does not prohibit **genuine new** low-level I1/I2/I3 events caused by interactions of new originals with old ones.
18. K4 cuts 10/22 remain possible actual auxiliary events, not projected away.
19. Physical new original columns still require complete K-free mixed-neighbourhood/left-density certificates, separately handled in Tracks A/B.
20. Full recursively coherent resolved macrodiary, common labelled inverse-source monoid orbit, uniform BRD upper/lower equality and exact counts remain OPEN.

## Lean targets / progress boundary

Aim for `Kk/HighCutClosureStratification.lean` with:
1. generic high-cut closure membership stability H1;
2. generic real Kpt I1/I2 and full physical relation invariance H2;
3. repaired physical next-stage pre-cut specialization H3;
4. actual cross-height old-to-new AlgorithmRun *all-cut* H4.

English committed before Lean. Direct exact-head `lake build` and strict standard-only named transitive-axiom reports, independent full project run; no protected manuscript, central imports or validation marks changed.
