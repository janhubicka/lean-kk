# Track F — monotone raw-capacity restriction / deletion locality (English first)

**14 November 2026; adversarial proof before Lean.** Stacked on [literal-column PR #130](https://github.com/janhubicka/lean-kk/pull/130), which defines actual chronological word raw bounds and proves they are support-monotone. The independent [deletion regression PR #35](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/pull/35) exhausts 223,092 finite canonical-deletion checks and exhibits the counterexample without monotonicity.

## Exact finite theorem in the existing Lean integer-witness API

Fix the actual `IntegerGraphSupport d ell` finite nonempty-support type (card ≤ell−1), `ell>0`, and any *two arbitrary raw capacity functions*
`B,C : IntegerGraphSupport d ell → Nat`.

Suppose each is **support-monotone**:
`B(S)≤B(V)` and `C(S)≤C(V)` whenever `S subseteq V` are admissible nonempty supports.

Fix a nonempty admissible support T and assume B and C agree on **every admissible nonempty U⊆T**. Then the actual normalized integer-clique-vector canonicalizers agree on T:

`integerGraphAgeCanonical d ell B T = integerGraphAgeCanonical d ell C T.`

This theorem is stronger than a trivial equality for B=C: the raw systems can be unrelated **outside** T, and they need not themselves be graph ages. It is precisely the raw-subfront invariance required before reindexing deletion of a coded branch.

## Proof, retaining every global support constraint

For one direction, choose an arbitrary **normalized B-feasible** multiplicity vector w (total ≤ell−1) and *zero all weights outside T* to produce w_T. Every coordinate of w_T is at most the original, so it still has total ≤ell−1. For any admissible nonempty V, write Q=V∩T.

- If Q is empty, its total under w_T is zero and automatically satisfies C(V).
- If Q is nonempty, its cardinal is at most |V|≤ell−1, so it is a genuine integer-graph support. By zeroing, the V-mass of w_T equals the Q-mass of w, which is ≤B(Q) by B-feasibility. Because Q⊆T, agreement says B(Q)=C(Q). By C-monotonicity Q⊆V, C(Q)≤C(V). Thus w_T respects C on every full V.

Also the T-mass is unchanged by zeroing. Therefore for each B-feasible w, its T-mass is ≤G_C(T). Taking the supremum over all B-feasible w proves G_B(T)≤G_C(T). Swap B,C and use B-monotonicity for the reverse inequality.

The proof is valid even when a raw bound has a zero, even when its canonicalization is not a positive graph age, and regardless of raw slack B≠G_B: the normalized finite supremum and zero weight are still defined for ell>0. No new Ramsey or Fraïssé hypothesis.

## Adversarial counterexample and limits

1. **Raw monotonicity cannot be omitted.** For K4 with two sorts, B({0})=B({1})=3 and B({0,1})=1, deleting coordinate 1 *before* canonicalization gives singleton capacity 3, but full G_B({0})=1. This is the explicit verified regression obstruction.
2. **Agreement only at T is insufficient.** An overlapping proper sub-support U⊊T may impose a stricter raw constraint and change G(T); require agreement on *all* nonempty U⊆T, not only at T.
3. **Finiteness and total-weight:** Normalized integer clique weights total ≤ell−1; this is exactly the witness universe already formalized in `IntegerWitnessCanonical`. The proof never assumes arbitrarily many witnesses or an unbounded sum.
4. **Intersection empty:** Do not manufacture an `IntegerGraphSupport` from an empty Q. Treat its mass as zero in a separate case.
5. **Canonicalization vs physical realization:** This is purely an abstract sorted L-clique profile theorem. It does not realize any prescribed relative numerical-H source or full parameter-closed B3 event.
6. **Dimension change still separate:** This establishes *support-locality on the same full finite sort set*. To obtain the published coding-deletion identity on `d−1` surviving sorts, one must additionally prove the finite reindexing/zero-extension equivalence along the survivor injection and the identity between literal restricted word columns and the restricted raw bound. The independent finite test confirms these, but do not call the full deletion lemma Lean-certified until those maps are formalized.
7. **Word raw monotonicity is independently proved:** The new Track F `trackFWordRaw_monotone` (PR #130) gives the hypotheses for actual chronological words; without this theorem one would be silently assuming monotonicity of arbitrary raw bounds.
8. **Coding and inverse remain open:** This lemma does not prove the word E/passing-bit equivalence, non-free splitting, chronology-respecting full inverse, or new independent unavoidability.

## Proposed Lean endpoints

New module `Kk/TrackFMonotoneRawLocality.lean`:

- `trackFZeroOutside` (a concrete normalized clique weight with all coordinates outside T set to zero);
- `trackFZeroOutside_T_mass` (T-mass unchanged) and `trackFZeroOutside_le` (all support masses weakly decrease);
- `trackFZeroOutside_feasible_of_agree`: one-directional feasible-vector transfer from B to C under C-monotonicity;
- `trackFCanonical_locality_of_monotone`: equality of canonical T capacities under two-sided monotonicity and agreement on supports inside T.

After English audit, compile the new module on its own exact head, run the existing strict standard-only named-axiom parser and full project build; do not modify global `Kk.lean` or manuscript validation marks. The full deleted-coordinate finite reindexing remains its own next theorem.
