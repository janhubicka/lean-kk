# Track D — removing the redundant marked-source nonemptiness premise
15 November 2026 — English-first proof and hostile hypothesis audit.

## Background
The existing checked `Kk/B3CutVisibleTransfer.lean` proves that full
corrected-(B3) follows from marked corrected-(B3), provided:
(i) the marked chosen source is nonempty, and
(ii) EVERY genuine cut-eligible full name physically adjacent to the cut
has its COMPLETE next-cut directed ordinary-L type among the ACTUAL CHOSEN
marked output types. The proof extracts one K_ell clique containing the
cut from any failed full test, and matches the genuine lower L-socle
using a marked chosen source.

The separate checked
`henson_failedSelectedB3_has_eligible_cut_neighbour` (in
`Kk/B3CutStarNormalForm.lean`) proves that failed full corrected-(B3)
FORCES at least one such genuine eligible positively cut-adjacent full
name, with no no-(I2) assumption. Consequently, condition (ii) ALONE
provides a member of the marked chosen source precisely in the only
case where it is needed. Nonemptiness is a *derived consequence in the
failure case*, not an independent global input.

## Exact theorem (English)

Let ell>=2 and ell<=k+1. Let E be symmetric, loop-free and K_ell-free,
and let A be a finite numerical-H structure over E. Fix cut<N, a finite
list of actual originals original: Fin M -> Fin N, and any predicates
Full, Marked on that list.

Let F be `selectedStagePoolPrescribedData A cut original Full`
and G its Marked analogue.

Assume:
(1) For EVERY v in Full with cut+1 <= freeLevel(original(v)) and
    actual positive physical L(cut, original(v)), there is a genuine
    chosen T in G.source such that the COMPLETE directed next-cut
    ordinary-L reduct of G.target(T) equals the corresponding physical
    type of original(v).
(2) G.CorrectedB3 for the normalized Henson family.

THEN F.CorrectedB3. No assumption that G.source is nonempty is needed.

## Proof

Suppose instead that F fails corrected B3.
Use `henson_failedSelectedB3_has_eligible_cut_neighbour` to obtain
one actual name v with Full(v), genuine cut eligibility, and positive
ordinary L(cut, original(v)). Apply (1) to v to get T in G.source
and equality of complete directed next-cut L types. In particular,
G.source is now nonempty. Apply the existing checked theorem
`henson_fullB3_of_cut_visible_complete_outputs`, which takes
exactly this marked nonempty witness, the original (1) coverage,
and (2), to conclude F.CorrectedB3. Contradiction.

The negative-cut case is a second useful corollary:
if NO full selected cut-eligible original has positive L adjacency to
the tested cut, then F.CorrectedB3, again with no no-(I2) premise.
This follows by contraposition from the checked genuine cut-neighbor
extraction. It handles dummy/fake and other genuine negative-cut
cases once their actual physical no-neighbor premises are established.

The converse contrapositive theorem says: under (1), any full failure
forces the marked test to fail, without a marked nonempty premise.

## Adversarial checks

1. Do NOT weaken (1) to selected graph-age equality or equal passing-number
   masks. The K4 numerical-H cut-10 auxiliary parameter counterexample
   defeats the selected-only shortcut.
2. Do NOT infer chosen target equality from having Marked(v): the
   prescribed map deduplicates complete old L+ source types by choice.
3. Do NOT require no-(I2) for this abstract transfer; it is only
   needed when deriving (1) from matching represented physical names.
4. Cut eligibility is `cut+1 <= freeLevel(original(v))`, not merely
   positive E at a different prefix.
5. The cut index must satisfy cut<N. Avoid confusing free cut levels
   with the forbidden clique parameter ell.
6. Full/Marked need NOT be subsets of one another: uniform (1) is the
   only matching premise.
7. In the empty marked-source case, (1) implies there are NO eligible
   positive full names. Therefore the full test passes by its own
   no-neighbour corollary. No vacuous proof of a false implication.
8. Same-initial-L old socles are recovered only after deriving a genuine
   chosen marked source T from a failed full test.
9. An extracted L-only clique has freely chosen upper-upper edges. Do
   not infer physical E or equality of arbitrary upper-upper atoms.
10. No general graph-age loss, common labelled inverse orbit, or
    entire independent-set full-boringness statement is derived.
11. For the small-independent application, **still prove** physical
    name exhaustion, all upper-types-chosen coverage (1) at EACH omitted
    cut, and no-(I1)/(I2) in its actual pre-cut closure.
12. The associated old-source arguments belong to one exact finite
    Henson numerical-H occurrence, not an arbitrary partially labelled
    forbidden-relational structure.
13. Register both the new source theorem and the no-neighbor corollary
    in a dedicated exact-head strict axiom gate before paper upgrade.
14. Keep existing conditional full-cut-star and global diary caveats.
    Do not remove prior counterexample tests or already validated
    historical theorem names.

## Planned Lean implementation

Create `Kk/B3CutVisibleNoNonempty.lean` importing the checked transfer
and cut-star normalization. The main proof is `by_contra`, obtain an
eligible positive selected original from failure, derive G.source witness
using the original coverage, then invoke the existing verified transfer.
The no-neighbor corollary is an immediate contradiction using the same
failure extraction. The contrapositive is a one-line consequence.
Dedicated strict axiom check should use only Lean standard axioms.

This is an independently useful finite simplification; it does NOT
discharge the graph-specific full boringness lemma by itself.
