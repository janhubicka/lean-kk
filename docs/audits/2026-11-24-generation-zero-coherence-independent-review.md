# Independent review: generation-zero coherence before implementation

## Reviewed proposal

Date: 24 November 2026. Independent reviewer: the adversarial audit task,
separate from the proposal's author.

Reviewed source:
`docs/generation_zero_stage_coherence_english_20261124.md`, including its
nonvacuity and necessity section. SHA-256 of the reviewed proposal:
`897830eeaf5954f6284e84cefd8a1b25b016a23e047b8ec2e8f6b50df5b62cab`.

The mathematical implication is approved for formalization. No Lean source
for this result had been implemented or checked when this review was made.
This approval is for the explicitly stated local theorem and its proof, not
for completion of the resolved-Q construction or the global characterisation.

## Checked deductions

1. The one-sort sigma is the canonical capacity of the actual finite old
   column `p ↦ E(p,j)` on **all** bases `p<b`. The two uses of
   `k4_canonical_singleton_le_two_iff_old_neighbour` are literal: a positive
   bit at b makes the after-prefix singleton at most 2; equality transfers
   that inequality to the before-prefix singleton and supplies an actual
   old p<b. No old witness is being assumed or inferred from an arbitrary
   stipulated label.
2. The first positive physical cut bit decodes a canonical later real name.
   The bounded whole-stage role theorem forces it to selected TOP. This
   uses the existing lower-cut decoder at g=0 with k>0; it does not extend
   the positive-generation old-coordinate argument across its g=0 boundary.
3. The witness coordinate `p(p,0)` is strictly old and genuinely within the
   finite numerical carrier because it precedes the tested cut. Its positive
   TOP bit transfers to the second original through equality of complete
   old types. Eligibility at the tested cut implies eligibility at this
   old coordinate.
4. Decoding the second original from its positive **old** bit is necessary.
   Without it, the proof would have silently assumed a real-address shape
   for every eligible original. The proposed proof makes no such assumption.
5. The dummy case contradicts ordinary symmetry and dummy isolation. In the
   retained-auxiliary case, bounded numerical order first gives j'≥b;
   equality contradicts the omitted role at b, and strict inequality allows
   the existing block-separation theorem. That theorem's non-dummy input and
   interval-modulo-dummies hypothesis are both present.
6. In the selected-TOP case, mere address order would only give j'≥b. The
   proposal correctly excludes j'=b, and every j'≤b, by the exact TOP free
   level `p(j'-1,k)+1`. The decoded earlier witness ensures j'>0, so the
   predecessor-base formula has its required endpoint hypothesis.
7. For two later selected TOPs, complete old type equality determines every
   base column `E(q,j)` with q<b by reading the actual coordinate p(q,0).
   The separate selected no-split premise then gives equality at b. Both
   generation-zero-to-TOP gates are open because k>0.
8. The full next-type conclusion follows through the already checked
   `full_equal_ordinary_cut_column_determines_next_type`. Incoming and
   outgoing auxiliary E bits are fixed by genuine eligibility and spacing;
   negative ordinary atoms and the common socle are preserved.

This proof covers the entire eligible root/Plan original pool. It does not
substitute the smaller closure-marked B3 tuple, and it assumes neither no-I1
nor no-I2. Existing structural transport can consequently be applied at a
positive real cut once its seed and actual-stage hypotheses are supplied.
At b=0, Lemma A correctly makes a positive neutral bit impossible; the
separate structural theorem's positive-cut requirement must still be kept.

## Construction interpretation

The manuscript subsection being audited is specifically the independent-set
construction in the K4-free Henson graph. The fixed parameter 4 in sigma is
appropriate there. It should not be advertised as the arbitrary-ell canonical
singleton without a corresponding generalized theorem.

Conditional on the construction's stated exact old-reference age and
old-column class invariant, the event argument is correct:

- Cover-block bits are constant on the classes from before the block.
  Equality of later old profiles implies equality of those earlier profiles.
- An omitted split cannot have selected terminals in both children of an
  old selected class, because that event would be retained as a selected
  split.
- The adjacency refinements precede a nonselected coding, so equal old
  selected profiles have equal coding bits.
- Equality of actual selected age across an omitted auxiliary block gives
  equality of each singleton capacity at the block endpoints. Monotonicity
  under enlarging the old prefix forces equality at each intervening member;
  the argument does not require the members to be adjacent in the order
  after isolated dummies are inserted.
- Controlled nonselected coding preserves the selected survivor age, while
  selected independent coding adds a zero bit to each selected survivor.

This reasoning does **not** prove that the infinite resolved-Q construction
maintains the invariant, nor that the actual AlgorithmRun stage is contained
in the intended Plan. Those remain separate obligations. The physical theorem
is useful because it reduces a missing full-stage structural property to two
explicit ordinary construction properties, rather than assuming that
structural property itself.

## Nonvacuity and necessity examples

The proposed k=2, N=35 example is consistent. Its selected TOP addresses are
22 and 28, its dummy cap is 34, and their free levels are respectively
17, 23 and 29. At cut 12 all are eligible. The two selected ordinary old
columns agree, their new bits are true, and the cap is separated by the old
positive coordinate 6. For each selected base the positive old pool changes
from {1} to the independent set {1,2}; its clique capacity stays 1, so sigma
stays 2. The base graph is bipartite and the auxiliary axioms are vacuous.

Deleting edge {2,4} leaves both singleton capacities unchanged but makes the
new selected bits different while the complete old types remain equal. Thus
singleton neutrality alone cannot replace no-split. The published 23 November
cap example gives the converse warning: selected no-split holds there but the
singleton drops from 3 to 2, and the cap comparison fails. Both premises do
real work. Neither example is claimed to realize an exact AlgorithmRun stage.

## Formalization requirements

The implementation should retain the exact actual finite-prefix definition
of sigma, bounded generations in both role contracts, k>0, tested-cut carrier
bound, non-dummy omitted role, the stated block interval condition, the
selected no-split and singleton-neutrality inputs, and whole-stage eligibility.
It should derive the old witness and all structural conclusions rather than
reintroduce them as new assumptions. Publication should retain the distinction
between this checked local implication and the still-open construction,
chosen-B3, odd-cut, common-source and global canonisation obligations.

## Initial implementation fidelity review

After the English checkpoint was committed, the independent reviewer read
`Kk/GenerationZeroStageCoherence.lean` and `Kk/GenerationZeroStructural.lean`
against this proposal. The implementation retains the explicit actual
one-sort capacity, both bounded role contracts, whole-stage eligibility,
the real old-coordinate witness, and the exact free-level exclusion of a
same-base TOP. The structural theorem allows arbitrary represented seeds,
retains the positive-cut and no-seed hypotheses, and derives both structural
verdicts. The skip theorem retains the actual chosen marked-B3 input.
No source-level change to the mathematical scope was found. Compiler and
transitive-axiom execution remain separate validation steps.
