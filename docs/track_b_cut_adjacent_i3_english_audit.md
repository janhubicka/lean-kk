# KK-free Track B — nonstructural I3 requires an UNMARKED CUT-ADJACENT genuine source original
**13 November 2026 — English proof and adversarial audit, committed before Lean.**

## Precise progress over merged Track B and Track D

Merged Track B PR #100 proves that a genuine positive nonstructural Algorithm 5.4 (I3) cut with a passing eligible marked corrected-(B3) test has a full closure-selected original whose **complete upper ordinary-L reduct** is not permitted by the marked source. The witness need not be proven adjacent to the tested cut.

Merged Track D PR #98 proves a stronger *sufficient* transfer property in Henson’s K_ell-free class: for two selected-original pools in one literal finite numerical H and a nonempty marked pool consisting of genuinely represented closure names, **no (I2)** forces complete next-L+ fibre coherence. Consequently the marked corrected-B3 test transfers to full if the marked pool includes every full selected original whose complete next-level type is eligible and whose **actual undirected ordinary-L edge to the tested cut is positive**. It does NOT assume agreement of freely chosen upper–upper L-edges in an arbitrary B3 witness.

Together these prove a new **necessary** geometric obstruction that is sharper than the general omitted-upper-type diagnostic.

## Theorem A: represented full nonstructural (I3) source

Choose ell≥2, k with ell≤k+1, a symmetric loop-free K_ell-free actual original edge relation E, finite numerical-H carrier A=finiteNumericH(normalizedGraphModel E,k,N), a genuine Kpt source set Z, an actual named-original universe `original : Fin M → Fin N` representing *every* node of Z by a prefix of a real Kpt original, and a positive tested cut c<N.

Exclude BOTH structural events:
* (I1) no node of Z is at level c;
* (I2) no two same-component nodes of Z have meet at level c.

Suppose the true `IsInterestingAt` predicate holds. Define the **full selection predicate**
`Full(v) := closureSelectedOriginal family A hAvoidA original Z c v`, not all ambient names with positive free cut.

Let `Marked : Fin M→Prop` be a **nonempty** selection of names that genuinely represent closure-crossing nodes: every marked v satisfies Full(v). Suppose its genuine `selectedStagePoolPrescribedData A c original Marked` passes corrected-B3.

Then there exists `v : Fin M` such that:

1. `Full v`;
2. `c+1 ≤ A.freeLevel (original v)` (real cut eligibility);
3. `A.L.binary c (original v) = true`, the REAL POSITIVE edge from the tested cut to the source original, including both-direction L consistency in the undirected Henson specialization;
4. `¬Marked v`.

### English proof

The verified successor-tree `algorithmI3_failsCorrectedB3` uses the *full actual closure source*, finite original pool representation and no-I1/no-I2 to show that its corrected-(B3) test fails at this genuine interesting stage.

Assume no such unmarked cut-neighbour exists. For EVERY full selected name v with positive cut eligibility and actual positive cut edge, classical excluded middle then forces Marked(v). That is exactly `hAllCutNeighboursMarked` in the checked Track D `henson_fullB3_of_no_i2_marked_closure_cut_neighbours`. By the hypotheses, every marked name has a genuine closure-crossing representative, the marked pool is nonempty, no-(I2) holds on the SAME Z, and marked corrected B3 passes. Track D therefore gives PASSING corrected B3 for the full source. This contradicts the first paragraph. Hence the four-clause witness exists.

This is an existence theorem about an omitted cut-ADJACENT source original, not a claim that all marked/front age vectors determine full B3. In the actual K4 cut-10 microevent, one cannot silently assume the marked-only x=38 profile covers q2=22.

## Theorem B: genuine AlgorithmRun source

Take an actual `R : SMTree.Envelope.AlgorithmRun` with selected c∈R.I 0, positive c<top, and real top-height seed. Set exactly
`Z := SMTree.Envelope.closure (admissibleKptSTree family) (R.I (c+1)) X`.
The checked `R.finalLevel_interesting_of_run` together with `R.I_succ_eq_higher_final_of_run` gives `IsInterestingAt Z c`. Apply A; the hypotheses include representation of EVERY z∈Z by one same named-original pool. No independent assumption of B3 failure or interestingness remains.

## Theorem C: genuine finite numerical-H AlgorithmRun maintained pool

Specialize to the actual Henson forbidden family `hensonForbiddenFamily ell hell`. Assume the real seed pool `U : Finset (Fin N)` and `X⊆ambientPrefixPool ... U`. Obtain full finite numerical-H forbidden-family avoidance from the original graph's no-loops, symmetry and K_ell-freeness, using the verified normalized-family equivalence.

Define `V := hStageOriginals (normalizedGraphModel E) k N U (R.I 0)` and the genuine enumeration `hOriginalName V : Fin V.card → Fin N`. Use the verified `numericH_algorithmRun_closure_original_in_final_pool` and `V.equivFin` to prove the common pool representation hypothesis of B. Conclude the omitted original lies in **this actual maintained V**, is genuinely selected by the full pre-cut closure and has a positive ordinary-L edge to the cut, but is not Marked. No artificial Fin N all-eligible pool.

## Hostile audit / exact limitations

1. **Cut-adjacency, not arbitrary upper omission:** this conclusion genuinely uses the K_ell-free graph-specific Track D small-clique-core theorem, not just a generic `PrescribedBoringData` reduct-transfer contrapositive.
2. **No-I2 only on the actual Z:** the fibre coherence proof fails with a competing meet at c; do not weaken it to a selected-front no-meet condition.
3. **I1 independently excluded:** interestingness can be structural; do not classify arbitrary marked levels as I3.
4. **Marked represented:** every marked name must represent some genuine Z-crossing source; merely being in V or being eligible is not enough.
5. **Marked nonempty:** the corrected-B3 predicate on an empty source is vacuously true and cannot cover any forbidden witness.
6. **Full selected source:** `Full=closureSelectedOriginal`, not all original names, not all chosen marked diary branches, and not all E-positive fake coordinates.
7. **Name-level conclusion:** `¬Marked v` is about a particular label, not a proof that the associated complete upper L-reduct is globally new; the older Track B result gives the latter for some (possibly different) source name.
8. **Cut edge is an actual ordinary L atom:** an incoming E/free-level bit cannot substitute for the positive L-edge.
9. **Future–future edges arbitrary:** no step equates the arbitrary B3 continuation's upper–upper edges to the physical ambient E or L edges.
10. **Finite source:** no conclusion about the unbounded resolved-copy stage or its ability to keep the same labelled source across diary occurrences.
11. **Top seed:** real AlgorithmRun selection implies genuine interestingness only with the displayed top-height seed and cut<top hypotheses.
12. **Final finite pool:** R.I 0 is used for final names V; the pre-cut closure uses R.I(c+1), not R.I 0.
13. **Physical K_ell assumptions:** no-loops/symmetry/clique avoidance, ell≥2 and ell≤k+1 are all explicit and indispensable to the Track D reduction.
14. **Duplicate type representatives:** Track D's no-I2 theorem compares complete *next L+* records of genuine represented names sharing old types; do not replace by an unverified chosen-representative identity.
15. **Not a diary normal form:** the missing named neighbour might itself be auxiliary; this is exactly why selected macro-age is insufficient.
16. **No global Ramsey conclusion:** full B3 matching, relative-profile fidelity, event-indexed labelled inverse source orbit, exact upper/lower big Ramsey bounds remain unproved.

## Formal verification gate

Three proposed new actual source/run/numerical-H theorem endpoints in `Kk/B3CutAdjacentI3.lean` and `Kk/B3CutAdjacentRun.lean`, preceded by this English proof. Existing current main `888cbd8d7d68e7d1839cada300148f25d57b2b35` passed hosted full Lean CI and contains Track G's **472** named axiom reports. Require new exact-head full `lake build`, parser self-test, **475** named standard-only transitive-axiom reports. No manuscript black prose or global green validation change.
