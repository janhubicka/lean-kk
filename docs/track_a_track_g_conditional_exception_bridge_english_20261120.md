# Track A ↔ Track G: conditional localization of selected-level discrepancies

20 November 2026. English-first proof and adversarial dependency audit.
**This is a conditional bridge, not proof that the proposed KK-free
macrodiary yields the required dependent source-profile matching.**
Do not promote any manuscript mark on the strength of this note.

## Generic exception-set lemma for actual successor-tree scans

Let H be a genuine SMTree with STree S. Let X,Y be *possibly distinct*
seed sets in the same H. Let R_X and R_Y be actual
`SMTree.Envelope.AlgorithmRun`s with the SAME finite top `N`.
Fix any exceptional set of natural cut coordinates `C`.

For every `i<N`, let `D_X(i)` denote the genuine
`IsInterestingAt H (closure S (R_X.I (i+1)) X) i` statement, and
likewise `D_Y(i)` using the **actual** Y-run tail and its own pre-cut
closure. Assume only

    forall i<N with i notin C,  D_X(i) iff D_Y(i).

Then

    (R_X.I 0 symmetric_difference R_Y.I 0) subset C.

In particular if `C` is finite, the number of selected cut
coordinates on which the two scans disagree is at most `|C|`.
No equality of full selected I-sets is asserted: chosen levels inside
C can change the tails and the closures used at lower cuts.

### Proof

The defining AlgorithmRun recursion starts at `I(N)=empty`. At cut
`i<N`, if the genuine pre-cut closure is interesting, the step inserts
**exactly the level i** into `I(i+1)`. Otherwise the step leaves
`I(i+1)` unchanged. Thus for each `i<N` the final selected set
`I(0)` contains the level `i` iff the genuine interestingness test
at cut i was positive: higher steps insert levels >i, and subsequent
lower steps insert levels <i, so no other step can add/remove i.
The representation also gives `I(0) subset {0,...,N-1}`.
Consequently for `i notin C`, the assumed equivalence of genuine
interestingness decisions yields exactly equal membership of `i`
in the two final selected sets. This is equivalent to the stated
symmetric-difference inclusion. The cardinality bound follows by
finite-set monotonicity.

**Lean API audit still needed:** the proof should derive the
per-level membership iff from the concrete `AlgorithmRun.topI`,
`interesting_step`, `noninteresting_step` and its verified bounds
on selected levels, not postulate a new independent recursion axiom.

## Application to genuine dependent Kpt profiles

Take H to be `normalizedKptSMTree family`, and use the same aligned
cut coordinates and scan top for both runs. At every cut outside C,
suppose the **actual pre-cut parameter closures** satisfy:

1. equivalent `KptI1AtCut` terminal-node flags;
2. exactly equal `FullPhysicalClosureCrossing` relations of
   old/upper dependent partial `L^+/E` ancestor pairs.

The already merged Track G theorem
`kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq`
(`Kk/TrackGFullEventProfileTransport.lean`) converts these two
properties to `D_X(i) iff D_Y(i)` at that actual cut. Applying the
generic exception-set lemma yields the symmetric-difference bound.

This uses the **full** crossing relation, including potential I2
forks and the auxiliary E records. Its exactness also handles the
I3 monoid skip-law, as established by Track G; no L-only projected
crossing or terminal-free shadow is substituted.

## Instantiate the exceptional set using Track A

Fix a genuine Henson original E with forbidden K_ell avoided, a
current original b, and the SAME later original TOP family j. The
new Track A schedule is the finite set

    C = { cap_E(P_U) :
          U nonempty admissible,
          b is U-eligible,
          cap_E(S_U)=cap_E(P_U) }.

The two-vertex forbidden clique argument shows

    C subset range(ell-2),   |C| <= ell-2.

**Conditional conclusion.** If the genuine Kpt terminal and full
old/upper L+/E crossing profiles of the two actual runs agree at
every aligned cut outside this C, then their final sets of selected
Kpt levels differ on at most ell-2 cut coordinates, irrespective of
how many future sorts are named.

This bound is NOT a bound on the number of all Kpt interesting
levels in either scan separately. Both scans might select many of the
same auxiliary levels outside C. Nor is it an assertion that full
Kpt profiles agree merely because ordinary-L raw ages agree. The
profile-equality premises remain the critical open diary-to-source
step; their proof may require new microdiary/parameter-closure data.

## Adversarial checks

1. Replacing the two complete full-L+/E physical crossing relations
   by ordinary-L raw ages makes the hypothesis false as a sufficient
   source comparison: I1 terminals and I2/I3 auxiliary information
   are then lost.
2. Terminal flags are independent inputs. Full crossing pairs alone
   miss nodes terminating at the cut.
3. All profile comparisons are at the SAME cut in the SAME normalized
   Kpt tree, and at the **actual pre-cut closures of the two runs**;
   comparing initial seeds or a chosen shadow would not suffice.
4. No bijection, injection or same cardinality of the two Kpt source
   sets is needed; physical pairs are matched extensionally.
5. This is NOT Track G349's unconditional full selected-scan equality:
   its hypotheses require profile matching at every cut. Here
   matching is required only outside a named exceptional set, and
   the conclusion is correspondence only outside that set.
6. The exceptional C is defined entirely from the fixed original
   graph; proving that new diary occurrences supply the profile
   comparison outside C remains genuinely new mathematical work.
7. The symmetric difference bound counts disagreements, not the
   total number of selected levels or the BRD.
8. If top=0 the final selected sets are empty; no off-by-one
   assumptions are hidden.
9. Without a guarantee that both scan-top coordinates align, an
   entirely separate height reindexing is required.
10. Do not insert this as a fully verified claim into the manuscript
    without the generic per-level AlgorithmRun membership lemma
    and the exact cross-track Lean application being kernel-checked.

## Next Lean deliverable after the Track A gate

Formalize a generic
`actualAlgorithmRuns_selected_symmDiff_subset_of_decisions_off`,
then instantiate it via
`kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq`
and `trackA_henson_critical_generation_card_le`.
The missing **non-conditional** bridge to prove is that the proposed
refined diary guarantees terminal and complete physical L+/E
crossing equality at every cut outside C. This is a proof obligation,
not something already established by the ordinary age calculation.
