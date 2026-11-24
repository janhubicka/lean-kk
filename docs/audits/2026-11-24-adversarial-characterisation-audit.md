# Independent adversarial audit of the published characterisation continuation

## Verdict and scope

Audit date: 24 November 2026. Audited Lean revision:
`ddb01a336e60d51ce0db289f0c3ab327a14635d8`, the published head of
[PR #512](https://github.com/janhubicka/lean-kk/pull/512).

The six new modules and the eight declarations repaired by commit
`7337955d37f386d2ef0e7c27abb96b234e892bd3` are mathematically sound within their
stated scope. This independent source review found no incorrect implication,
missing endpoint case, replacement of complete types by graph ages, or circular
use of no-I2 in the new structural proof. It also found no proof of the complete
characterisation in this continuation. The local implications must not be
reported as a global upper bound or an ordinary big Ramsey degree equality.

This audit inspected the theorem statements, their proofs, the four repaired
interfaces, and the actual upstream definitions of partial types, complete next
columns, closure, maintained original pools, and AlgorithmRun. Upstream sources
were read from successor-tree-lean at the dependency pinned by this repository,
`a74c10761303a18649053f2af3a1a1697f032e13`.

No compiler or test build was run as part of this independent review. The
previous hosted kernel checks remain the separate validation evidence recorded
in `2026-11-23-upper-continuation-validation.md`. This review checks the meaning
and applicability of the formal statements in addition to that evidence.

## 1. The canonical-generation repair is necessary and complete

The real numerical address is

\[
 p(j,m)=2(k+1)j+2m.
\]

Consequently `p(j+1,0)=p(j,k+1)`, and a TOP of a later base also has an
out-of-range presentation over an earlier base. A role contract quantifying
over all natural m constrains these artificial presentations as well as the
canonical one. In particular, the old dummy-cap contract could force an
earlier selected coded base to be dummy. These were overly strong application
hypotheses, not false implications under their stated assumptions.

The patch consistently changes each applicable root and Plan contract to
require `m ≤ k`. TOP remains included. The four intermediate stage-role
declarations receive the corresponding bounded decoding input; the physical
neighbour consumers forward the bound already returned by the exact neighbour
decoder. The selected-coding skip wrappers also preserve the bound when lifting
the singleton root contract. I found no remaining unbounded invocation among
the eight repaired endpoints.

The two regressions in `Kk/RealPositionGenerationAliases.lean` verify actual
bounded role assignments and show that their unbounded counterparts are
inconsistent with those assignments. They establish consistency of the repaired
local contracts. They do not construct an AlgorithmRun or its proposed Plan.

## 2. Complete next-type uniqueness retains every atomic field

In `Kk/EqualCutFullType.lean`, both future originals are in the same enumerated
partial structure A and satisfy `cut+1 ≤ freeLevel`. This gives incoming
auxiliary E equal to true at the new coordinate, and outgoing E equal to false
by the actual spacing axiom. Equality of the ordinary cut bit, together with
symmetry, gives equality of both directed ordinary bits involving the future
vertex. All pairs between old socle coordinates and the new socle coordinate
are literally in the same A and therefore agree. The new diagonal agrees for
the same reason, while the unary dimension is zero.

The upstream `CompleteNextColumn` contains all six fields, including both
binary directions, both auxiliary E directions, unary data, and diagonal
data. Its row/column domains include the new-new pair. Together with equality
of the complete old dependent type, these fields exhaust the next type.

Thus the result is complete L+/E equality, including false ordinary bits. It
does not rely on equality of ages, on an arbitrary choice of upper target, or
on adding an invented E relation to an ordinary graph witness. The theorem
would not apply to two unrelated ambient structures merely because their
selected ordinary graphs are isomorphic.

## 3. Positive-generation coherence covers the entire eligible stage

In `Kk/PositiveGenerationStageCoherence.lean`, fix an omitted base b,
`g < k`, and the complete physical stage original pool. A positive ordinary
bit at `p(b,g)` forces a canonical later real name `p(j,m)` with
`b < j`, `g < m`, `m ≤ k`, and `E(b,j)=true`. The bounded role classification
then forces this name to a selected TOP, so `m=k`.

The same argument applies to positivity at `p(b,0)`. Since both generation
gates to TOP are open, the two bits are true simultaneously. The Boolean case
analysis also proves equality when the bits are false. This is an important
coverage point: the proof does not assume that every stage name is real and
then silently omit fake or zero-free names. It derives the real address only
when a positive bit requires one.

For `0 < g < k`, the coordinate `q=p(b,0)` is strictly below `c=p(b,g)`.
Complete old-type equality therefore includes equality of the ordinary
q-column. The copied-column result transfers this to equality at c, and the
complete next-type theorem applies. No selected independence, auxiliary-block
convexity, canonical age neutrality, or structural verdict is needed in this
positive-generation argument.

The bound `g>0` is essential to this particular inference. At g=0 the
copied-column equation becomes a tautology and gives no old information about
the new bit. The reviewed example in
`2026-11-23-positive-stage-nonvacuity-and-zero-boundary.md` has two selected
TOPs and a dummy cap with equal complete old types at the zero-generation cut,
but new ordinary bits `true,true,false`. Selected-only no-splitting therefore
does not suffice for coherence of the whole pool. The example is a physical
stage example, not an asserted exact run stage.

## 4. Auxiliary-block separation uses the right interval condition

`Kk/ResolvedQBlockSeparation.lean` excludes an old neighbour of a later retained
auxiliary original across an omitted **non-dummy** base. Earlier dummies have
zero rows; earlier coded bases cannot see a later auxiliary base; different
auxiliary blocks do not interact. If the earlier auxiliary lies in the same
block, convexity modulo dummies forces the intervening non-dummy base into
that block, and common block flags contradict its omission.

Both the modulo-dummy clause and the non-dummy hypothesis are material. For
example, auxiliary bases 0 and 2 in one retained block with dummy base 1
between them may have `E(0,2)=true`. Base 1 is omitted and the allowed interval
condition holds, but the later auxiliary's old column is not zero. The theorem
correctly does not make its conclusion at that dummy base. Its new cut column
is zero for a different reason, namely dummy isolation.

## 5. Structural transport handles generated nodes and endpoints

The proof in `Kk/StageCoherenceStructural.lean` has three logically separate
parts, and their order is sound.

First, two eligible same-component originals cannot meet at c when complete
old equality implies complete next equality. A meet at c gives equal ancestors
at c and unequal ancestors at c+1. The actual original-ancestor raw-type
identification then contradicts the coherence hypothesis.

Second, a full closure node at a positive even real c, if not a seed, is a meet
of two actual originals from the maintained whole stage. This uses the real
meet-and-parameter closure normal form. A parameter original has positive odd
free level and hence cannot itself end at the even real cut. For each original
meet witness the weak bound `c ≤ freeLevel` is strengthened to strict
eligibility by positivity and that parity theorem. Applying the first part
excludes I1. Seed absence remains explicit until it is discharged by the
literal TOP seed construction.

Third, exhaustive representation of each node of the same actual closure Z
supplies original representatives for both sides of a strict crossing fork.
The old and next type transports use those same nodes and those same
below-original proofs. Whole-stage coherence therefore excludes the strict
old-equal/next-different fork. No-I1 then converts this to no-I2.

The no-I1 premise in the last conversion must remain: if Z has a terminal z
at c, its self-meet `(z,z)` is an I2 witness even when no strict crossing fork
exists. The implementation handles this case by proving no-I1 first. It does
not infer eligibility from physical address order alone.

The finite stage enumeration uses exact `equivFin` inverse identities to
identify each actual original name. It does not infer literal name equality
from equality of partial types. Exhaustive source representation has no no-I2
premise, so no circularity enters this step.

## 6. Actual-run conclusions and remaining construction obligations

`Kk/PositiveGenerationStructural.lean` applies the above to the literal stage
`Run.I(c+1)`. Its generic structural result does not need `c<top`; it works for
the supplied level set. The nonselection corollary correctly retains `c<top`,
the top seed, the finite cut bound, the Henson hypotheses, and the **actual
chosen** Marked corrected-B3 verdict.

The TOP-seed specialization uses the real seed family: the cap original and
its ancestors at the selected TOP addresses. It proves source representation
and absence of positive lower-real seed endpoints. It does not replace the
cap by selected TOP originals or infer the actual run's Plan inclusion from
the desired conclusion.

The following obligations are still needed for the full characterisation:

1. Build the required resolved Q, role assignment and Plan from the proposed
   finite record, with all chronology, forbidden-clique and canonical-address
   hypotheses established for that construction.
2. Prove generation-zero whole-stage coherence, including comparisons of
   selected TOPs with eligible roots and retained auxiliaries. A construction
   must supply actual old distinguishing witnesses when a new TOP bit is
   positive; a selected-only age or no-split assertion is insufficient.
3. Prove the planned odd free-cut closure and the remaining actual chosen
   corrected-B3 verdicts. Coherence is a structural statement and is not
   itself the required age-preservation verdict.
4. Complete the descending induction that establishes
   `Run.I(c+1) ⊆ Plan`; supplying that inclusion as an input at each isolated
   cut does not prove the induction.
5. Establish common labelled complete-source identity, inverse-prefix/orbit
   identification and global upper canonisation. Local source coverage and
   pairwise coherence are not that identity theorem.
6. Supply the ordinary lower-occurrence/colouring argument required by the
   big Ramsey degree definition. The unavailable earlier local implementation
   is not validated by this branch or by finite history counts alone.

The comments in `Kk.lean` and the final continuation scope report explicitly
retain these limits. Historical English proposal files still contain their
original pre-implementation status text; the dated completed-validation report
is the status authority for the published modules.

## 7. Verification inventory inspected in this review

The focused audit contains exactly 25 distinct `#check` names and exactly the
same 25 `#print axioms` names in the same order. It covers 16 new public
declarations, all eight repaired declarations and the existing isolated-dummy
TOP-seed endpoint. All six new modules are imported by `Kk.lean`. The private
next-column extensionality helper is included transitively through its public
endpoint.

The focused workflow builds all ten affected modules. Its shell uses
`set -euo pipefail`, so a failing Lean invocation cannot be hidden by `tee`.
The parser compares exact report multiplicities and theorem names and permits
only `propext`, `Classical.choice`, and `Quot.sound`; it rejects missing,
duplicate, unexpected and custom-axiom reports. These source inspections do
not replace the separately recorded hosted execution results.

The appropriate validation marker remains a checked **conditional interface**
for the local results. No global characterisation or degree marker should be
promoted on the strength of this continuation alone.
