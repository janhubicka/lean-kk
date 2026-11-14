# Track C — actual AlgorithmRun selected levels are monotone under seed-set extension

**14 November 2026. English mathematical proof and 20 hostile checks BEFORE Lean.**
Stacked on Track C PR #192 (true new-root pre-cut closure absorption). Current successor-tree dependency `lean-successors` has the checked `IsInterestingAt` trichotomy and actual `AlgorithmRun` recursion; this proof does NOT change their axioms or use a hand-assumed monotonicity.

## Previously assumed retention becomes a theorem

The newly repaired next physical Kpt seed family is

```
Y = closure_I(X) ∪ {actual new Kpt original nodes}
```

so `X⊆Y`. Our prior closure-absorption theorem needs the old selected level set I to lie among the new run's selected levels ABOVE the cut. We previously kept retention `I⊆R_new.I0` as an explicit obligation.

There is a deeper **abstract** theorem: at the SAME scan height `top`, adding initial seeds never removes a level selected by actual Algorithm 5.4. Its proof uses monotonicity of the precise I1/I2/I3 definition, not an ordinary graph-age shortcut.

## M1 — genuine IsInterestingAt is monotone in its complete Kpt node set

For any SMTree H and two sets C⊆D of actual nodes, at any level i,

`IsInterestingAt H C i → IsInterestingAt H D i`.

Proof by the verified *three disjuncts*:
- (I1): an actual level-i node in C remains in D.
- (I2): an actual pair in the same root component with meet level i remains in D.
- (I3): if no one-level skipping map D0 realizes ALL old-to-next ancestors of **C**, then a map realizing every crossing of larger D would also realize all crossings of C, contradiction.

The I3 direction is important: failure of an ordinary L-only corrected B3 witness is **not** being asserted monotone by fiat; this is the ACTUAL successor-tree one-level map requirement on the same fixed SMTree and same i. No precompact graph expansion is assumed.

## M2 — meet/parameter closure monotone in BOTH seeds and selected level sets

For I⊆J and X⊆Y:

`closure S I X ⊆ closure S J Y`.

Proof: `closure S J Y` is meet-closed and J-parameter-closed, hence I-parameter-closed by the verified `ParameterClosedOver.mono_levels`. It contains X because X⊆Y⊆closure_J Y. Apply the least-closure theorem `closure_minimal` to the original I,X. No assumption about distributivity over unions.

## M3 — actual AlgorithmRun selected levels are monotone in initial seeds

Let `R : AlgorithmRun H X top` and `S : AlgorithmRun H Y top`, with X⊆Y and **identical** SMTree H and top.

**Theorem: for ALL i≤top, `R.I i ⊆ S.I i`.**

Prove by downward induction using the already checked `induction_down` recursion on levels. At i=top, both sets are `{top}` by the genuine AlgorithmRun top conditions. Assume `R.I(i+1)⊆S.I(i+1)`; M2 and X⊆Y imply the FULL pre-cut closure of R is a subset of that of S.

If R selects i because `IsInterestingAt` is true, M1 ensures S's larger actual closure is interesting. Both recursions insert i, and the induction hypothesis gives the new selected-set inclusion.

If R does NOT select i, the verified `R.noninteresting_step` gives `R.I i=R.I(i+1)`. For S, either it inserts i or does not; in BOTH cases `S.I(i+1)⊆S.I i` by its verified `level_step`. Combining gives `R.I i⊆S.I i`.

This proof **does not** require E1, finite-ness of X, existence of top seeds, forbidden-free age assumptions or a selected graph shadow. It is an abstract theorem about ACTUAL AlgorithmRuns and their full closure/one-level map semantics.

## M4 — new-root repaired stage automatically retains old same-height selected levels

Let `Rold : AlgorithmRun H X top`, and let `Rnew` be any genuine run with SAME top on the corrected physical next seeds

`Y=closure (admissibleKptSTree family) (Rold.I0) X ∪ image(new actual Kpt originals W)`.

Because `X⊆closure_{Rold.I0} X⊆Y`, M3 implies

`Rold.I0 ⊆ Rnew.I0`.

This is the previously UNPROVED same-height retention premise, now discharged by the exact successor-tree trichotomy. It is a stronger result than merely initial-seed I1 preservation.

## M5 — unconditional (relative to same-height Rold) pre-cut source absorption BELOW the old selected levels

At any new-run tested cut `cut<top` strictly below **every** old selected level (`∀q∈Rold.I0,cut<q`), M4 gives retained old I, and the verified run-tail theorem yields

`Rold.I0 ⊆ Rnew.I(cut+1)`.

The earlier PR #192 absorption theorem now concludes

```
closure_{Rnew.I(cut+1)}(Y)
   =
closure_{Rnew.I(cut+1)}(X ∪ image(new actual Kpt originals W)).
```

Hence the actual I1, I2 and entire complete physical old/upper L+ crossing relation at the cut also agree, by PR #192.

This is the first **proved** elimination of the inherited closure's potential artificial additional parameter events at a genuine new-root cut under an explicit same-height old run.

## Hostile review

1. Both runs must use the SAME scan `top`. A prior run on a shorter original top is NOT automatically comparable with a new run on a greater height; no false across-height stability.
2. Both runs must use the exact SAME SMTree H and admissible Kpt successor structure; changing generation k changes physical data and may change seed sets.
3. The I3 monotonicity applies to **impossibility of a one-level map realizing all Kpt crossings**, not to a guessed ordinary L-age corrected B3 failure.
4. For I3, if a map serves the larger D, restricting its universally quantified crossing property to C⊆D serves C. Thus `interesting C → interesting D` is correct.
5. I1 and I2 witnesses remain in larger C; no attempt to distinguish trivial self-meets at I1, since the genuine IsInterestingAt uses both disjuncts.
6. The closure is the least simultaneously SAME-COMPONENT MEET and SELECTED-PARAMETER closed superset; arbitrary seed union closure distributivity is NOT assumed.
7. M2 uses BOTH `I⊆J` and `X⊆Y`, not just seed inclusion.
8. Downward induction needs `R.I(i+1)⊆S.I(i+1)`, not an unjustified equality. If S selects extra levels, its closure is strictly larger, which is allowed.
9. If the SMALL run is interesting, the LARGE run must be interesting by M1; the converse can fail (new seeds introduce new I1/I2/I3).
10. If SMALL run is boring, LARGE run may be interesting. We only require `S.I(i+1)⊆S.I i`; its precise case is irrelevant.
11. The top initial selected set is always `{top}`, even if no top seed exists. Thus the theorem does not smuggle a top-seed assumption.
12. The theorem does NOT imply two runs on *different* seed sets have equal selected levels, nor a common labelled inverse-source orbit.
13. For repaired stage Y, old X⊆Y because of verified `subset_closure`. This must be displayed, not assumed.
14. Old I in M4 must equal the actual `Rold.I0` of a SAME-HEIGHT old run. An arbitrary diary-prescribed old set I is not automatically that set.
15. In M5, every old q must be STRICTLY above tested cut, since selected-level tail `Rnew.I(cut+1)` drops levels ≤cut.
16. If old I contains 0, there is NO nonnegative cut strictly below all old levels, so the corollary may be vacuous for that stage; it is not a global all-cut simplification.
17. The repaired original-only seed construction MAY generate new selected-parameter lower nodes; M5 merely compares its closure with the minimal-seed closure under retained higher old levels.
18. The full I1/I2 and physical crossing relation equality is at the SAME actual new-run pre-cut. It does not synchronize a different diary occurrence's physical parameters.
19. K4 genuine microcuts 10/22 remain real; no selected-front approximation or false boringness.
20. New Henson backward column realization, full unbounded resolved macrodiary, common labelled inverse-source orbit, uniform bounds and exact BRD numbers remain OPEN.

## Lean targets and gates

Create `Kk/AlgorithmRunSeedMonotonicity.lean` with FIVE named endpoints: IsInterestingAt monotone, full closure monotone in both inputs, actual AlgorithmRun selection monotone, repaired new-root same-top retention, and pre-cut old-closure absorption from that retention. Use exact-head direct module build and FIVE strict standard-only transitive axiom reports plus full-project Lean CI. Keep central importer, shared axiom registry, manuscript black/olive text and validation marks unchanged.
