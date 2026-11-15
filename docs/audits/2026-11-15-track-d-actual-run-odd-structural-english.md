# Track D — selected odd physical cuts are necessarily structural

15 November 2026. English-first proof and adversarial audit (before Lean).

## The statement

Fix ell>=2, ell<=k+1, and a genuine finite numerical H of height k
over a symmetric, loop-free K_ell-free Boolean graph E. Let U be the
actual finite original seed list and X a true Kpt seed set represented
by U, with a seed at the genuine AlgorithmRun top. Let Run be a real
normalized Kpt SM-tree AlgorithmRun with top `top`.

For an ODD physical cut `c=2a+1` with `c<top`, `c<N`:
if `c ∈ Run.I 0` (selected by the TRUE algorithm), then either

- **(I1):** the ACTUAL pre-cut closure
  `Z_c=closure(admissibleKptSTree,Run.I(c+1),X)`
  contains a Kpt node at exact level c; or
- **(I2):** Z_c contains two same-component nodes meeting at c.

This is a genuine **actual-run dichotomy**; no selected-shadow
surrogate, no artificial pre-cut source, no nonempty Marked source and
no new forbidden-witness E expansion is used.

Equivalently, if neither I1 nor I2 occurs in the full Z_c, c is not
selected by Algorithm 5.4. It does NOT say that all odd cuts are
boring, because actual E/free-level parameter originals can force I1
(and pairs of nodes can force I2).

## English proof

Suppose c is selected but full I1 and I2 are absent.
The previously verified
`henson_actualRun_nonstructural_I3_has_exact_physical_core`
applies directly to the SAME finite numerical H and actual run:
its genuine top seed and selected positive cut give actual
nonstructural (I3) and a finite physically labelled forbidden core
for the full pre-cut source; this theorem has already discharged
the real maintained-pool exhaustiveness obligations.

The separate verified
`henson_actualRun_complete_fullB3_failure_iff_physical_bad_core`
turns that exact core back into failure of the *actual complete*
selected-stage corrected B3 test. There is no substitution by
an arbitrary selected original subpool.

Now the verified
`henson_failedSelectedB3_has_eligible_cut_neighbour`
finds a genuine selected physical original v with
`c+1<=freeLevel(original(v))` and real ordinary-L
`L(c,original(v))=true`.

But `c=2a+1` is physically ODD, and the checked
`hNumericBinary_odd_left_false` says
`L(2a+1,y)=false` for every numerical y, regardless of its auxiliary
E column. Contradiction.

The asserted (I1-or-I2) disjunction follows classically by taking
the contrapositive of this nonstructural-unselected implication.

## Hostile checks

1. The cut is an **actual odd numerical coordinate**, not an abstract
   successor-tree level that becomes odd after a monoid relabelling.
2. This is the TRUE AlgorithmRun for the full original pool, not
   selected diary branches; actual pre-cut Z is computed using
   `Run.I(c+1)`, while the maintained name carrier uses `Run.I 0`.
3. The selected cut c is strictly between 0 and top; oddness supplies
   `0<c`, and the hypotheses explicitly require `c<top` and `c<N`.
4. A genuine top source seed is supplied; without it, selected-run
   interestingness need not yield a physical I3 witness.
5. The normalized forbidden family is exactly that of K_ell-free
   undirected graphs; the physical clique-core theorem is not
   asserted for arbitrary relational languages.
6. All old-source and new-source L+ type atoms, including auxiliary E,
   are present in the verified actual-run full-source certification.
7. Structural priority is correct: a meet at c may be trivial when
   an I1 node is already present; the classification uses the
   inclusive disjunction (I1) or (I2), not an unconditional fork iff.
8. Failure of corrected B3 is converted using the verified actual-run
   physical-core equivalence under the independently assumed
   no-(I2) closure condition. No vacuous source nonemptiness inference.
9. Odd fake target E columns may be empty, while odd physical source
   coordinates can still be **E predecessors** for real parameters;
   therefore odd `L=0` does not imply no I1.
10. The total original list may contain auxiliary q2-like names;
    the contradiction forbids all positive ordinary-L cut neighbours,
    so no selected-only projection is hidden.
11. This theorem is independent of the still-pending standalone
    `henson_numericH_odd_cut_correctedB3` PR #223, and therefore
    provides a separate proof route and verification cross-check.
12. No top-generation or arbitrary real even-cut conclusion is made.
13. No labelled source orbit or big Ramsey degree is obtained.
14. The proof uses ONLY previously merged Lean theorem bodies.
    A fresh exact-head compilation and strict axiom gate are still
    mandatory before marking this new combined implication verified.
15. The small-independent (n<=3) application must still prove that
    its **retained cut set** contains every actual full-closure odd
    structural event. The present theorem alone does not bound them.
16. The finite cut-star obstruction remains an arbitrary L-only
    age witness; neither its upper-upper L bits nor any E bits are
    identified with physical numerical-H edges.

## Implementation

Add `Kk/ActualRunOddStructural.lean`, importing
`Kk/B3ActualI3PhysicalCore.lean`,
`Kk/NumericHStructuralCutClassifier.lean` and the checked H numeric
binary lemmas.

First theorem: under explicit no-(I1) and no-(I2) in genuine Z_c,
the odd selected cut assumption is impossible. Reuse actual-run
physical-core theorem + actual full-B3 iff, derive a positive eligible
cut neighbour and contradict `hNumericBinary_odd_left_false`.

Second theorem: under the real run/seed hypotheses, selection of
an odd c implies `KptI1AtCut family Z_c c \/
KptI2MeetAtCut family Z_c c`. Derive by classical by-cases
on the structural tests; no extra hypotheses.

Register both under fully qualified names in a dedicated exact-head
strict transitive-axiom gate (only standard Lean axioms). This is
one genuine structural component of the independent-set omitted-cut
argument, **not** the complete small-independent upper bound.
