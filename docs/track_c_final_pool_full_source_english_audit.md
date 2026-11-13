# Track C fourth stage — FULL source/upper type record on the final named run pool

**13 November 2026 — English mathematical proof and hostile review, BEFORE Lean.**

Earlier Track C stages provided an exact full-source interface over
`Fin N`. That is geometrically correct, but insufficient by itself
for a uniform Ramsey-degree count because N is the size of an
arbitrarily large finite numerical H+ prefix. The full algorithmic
induction instead tracks one SMALLER finite maintained name pool.
This note obtains the crossing record with exactly those names.

## C8. Named finite full-source crossing lemma

Let A=finiteNumericH K k N, let the fixed normalized family be
avoided by A.L, and fix ANY finite list of genuine numeric-H
addresses `original : Fin M → Fin N` (not assumed injective, but
the eventual construction uses a canonical enumeration). Let Z be
an arbitrary set of complete Kpt types such that

`∀ z∈Z, ∃v:Fin M, z ≤ A.kptOriginal family hAvoid (original v)`.

At a numerical cut p assume the ACTUAL full (I2)-exclusion

`¬∃a,b∈Z, SameComponent(a,b) ∧ lev(meet(a,b))=p`.

Define `F=closureSelectedBoringData family A hAvoid original Z p`.
Then F satisfies *both* source/crossing directions:

- `CoversClosureCrossing family Z p F` (every true source
  crossing is covered, including all meet/parameter closure nodes);
- `IsCrossingGraphOf family Z p F` (every prescribed source/upper
  pair really arises from a member of Z);
- for each `T∈F.source`, there is ONE `v:Fin M` whose target
  numeric position is actually **real**, `original v = iota(i,q)`,
  `q<=k`, with `p+1<=A.freeLevel(original v)`,
  `T=A.partialTypeAt p (original v)`, and
  `F.target T=A.partialTypeAt (p+1) (original v)`.

**English proof.** The first clause is the successor-tree
`closureSelectedBoringData_covers` specialized to the named
pool and the no-(I2) condition. For the second, unpack source
membership using `selectedStagePoolPrescribedData_source_original`,
obtaining one selected witness v. The selected predicate itself
contains a z∈Z strictly above p with z below the ORIGINAL Kpt type
at v. Consequently `kptBelowOriginal_ancestor_raw` identifies
both the p and p+1 ancestors of z with the complete old and upper
types of that SAME v. For the third, use the same selected source
witness, its strict free-cut inequality, and the already verified
`finiteNumericH_positive_freeLevel_has_real_target`. This
excludes fake *target representatives*, not fake predecessors.

## C9. ACTUAL AlgorithmRun final-stage pool, rather than all N names

Let U be a Finset of initial original names, X a genuine Kpt seed
set with prefix representation over U, and R a real AlgorithmRun
of height `top`. At a cut `p<top` let

`Z = closure (admissibleKptSTree family) (R.I (p+1)) X`,
`V = hStageOriginals K k N U (R.I 0)`,
`original = hOriginalName V : Fin V.card → Fin N`.

The pinned successor-tree theorem
`numericH_algorithmRun_closure_original_in_final_pool` proves
for EVERY z∈Z a target `v∈V` whose complete Kpt original is
above z. This uses the genuine run-tail and parameter-closure
invariants, not a postulated source-to-name function.
Reindex by the *actual* bijection `V.equivFin`; then the target
witness lies in `Fin V.card` and has literal numeric-H address
`hOriginalName V` of that label.

The named source lemma C8 now gives the **whole two-way crossing
correspondence and full upper L+ type assignment with a name in
`Fin V.card`**, provided that exact pre-cut closure has no
competing-(I2) meet.

Thus the source-name universe is controlled by `V.card`,
rather than the arbitrary ambient prefix size N. This is the
relevant interface for the `R(M)` signature capacity and
eventual finite carrier. This theorem **does not itself prove**
that `V.card` is bounded independently of the chosen H prefix;
that is part of the higher-generation numeric recurrence.

## Adversarial checks

1. The seed prefix representation `X ⊆ ambientPrefixPool ... U`
   is a true separate invariant for arbitrary recursive X; no
   silent assertion that all generated seeds are initial originals.
2. **Use the SAME run R** in Z and V. Replacing `R.I 0` by a
   different run loses the fixed-name bound.
3. The run-tail theorem is needed to show
   `R.I(p+1)⊆R.I 0`; an arbitrary chosen set I does not
   necessarily lie in the final stage.
4. V consists of U and ALL final selected positive-free-level
   numeric vertices, including auxiliary parameter originals.
   Dropping any of them may falsify closure representation.
5. The source labels have type `Fin V.card`. Replacing them by
   `Fin N` loses the intended signature-capacity bound.
6. The source F is `closureSelectedBoringData` with those exact
   source labels, not the marked-selected shadow.
7. No-(I2) is indispensable for every actual crossing to agree
   with the chosen F target. No-(I2) must hold on the full Z.
8. Source old and upper assigned types are from one and the
   same `original v`; do not select old and upper labels separately.
9. Positive free cut rules out fake TARGETS but not fake source
   predecessor coordinates inside the full L+ record.
10. Repeated input names are harmless for C8 but the canonical
    V enumeration gives distinct names and a controlled finite
    cardinality for the application.
11. K4 cuts 10 and 22 remain a regression against any claim that
    a selected-only profile determines the full source.
12. No unconditional corrected-B3 truth, common labelled
    inverse-source orbit, or complete BRD characterization is
    concluded from these finite source identities.

## Lean exports and gates

- `finiteNumericH_named_pool_cut_crossing_and_upper_types` (C8).
- `finiteNumericH_run_final_pool_crossing_and_upper_types` (C9).

The direct module `Kk/NumericHFinalPoolCrossing.lean` must build
and both declarations must pass strict exact standard-only
transitive-axiom checks; run the full project gate as well.
Do not modify the central `Kk.lean`, manuscript text or
validation marks before Track G integration.
