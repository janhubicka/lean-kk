# Track D: exact physical bad-core iff FULL corrected B3 in an actual Algorithm 5.4 run
14 November 2026 — English argument and hostile audit before Lean.

## Critical scope correction

The already kernel-checked
henson_fullB3_failure_iff_physical_cut_star_bad_core_of_no_I2
proves an exact iff for a *specified Selected original-name predicate*
whose names genuinely represent nodes in one closure Z. Its
hRepresented hypothesis is only a FORWARD inclusion:
Selected(v) -> closureSelectedOriginal(v). On its own, this does
NOT prove the caller's selected pool is the ENTIRE parameter-closed
AlgorithmRun source. We must not silently promote this general
selected-stage theorem to a whole-run theorem.

Track B's verified actualHensonRunCutOccurrence construction and its
two distinct validations close this gap:

(A) actualHensonRunCutOccurrence_fullExact states *both directions*:
for every maintained original name v,
P.Full(v) iff v represents an actual Kpt closure node in the true
pre-cut set Z = closure(... Run.I(cut+1) ...), strictly crossing cut.

(B) actualHensonRunCutOccurrence_poolExhaustive, assuming the actual
original-prefix X pool representation and cut<top, says EVERY z in Z
is a prefix of SOME original from the genuine maintained
hStageOriginals(... Run.I 0) pool, not a hand-selected subset.

Together these certify that the full source function
P.fullProfile = selectedStagePoolPrescribedData P.ambient cut
P.original P.Full covers the complete physical pre-cut closure.
No extra auxiliary E bits are attached to a finite age-test witness.

## New theorem (one concrete AlgorithmRun consequence)

Given ell>=2, k with ell<=k+1, a symmetric loop-free K_ell-free
base edge E, genuine finite numerical-H carrier N, an original seed
pool U and actual Kpt AlgorithmRun Run of seeds X at top, the
standard finite original-prefix hypothesis hX, a cut p<top,N, and
absence of actual (I2) meets in the *genuine pre-cut closure*:

let P := actualHensonRunCutOccurrence(... Run,p,...).

Then all THREE facts hold simultaneously:

1. P.Full is EXACTLY the genuine closure-selected predicate
   (not merely a represented subpredicate);
2. EVERY pre-cut closure node is physically represented by one
   maintained Run.I 0 original in P;
3. FAILURE of the full corrected-B3 test of P.fullProfile is
   EQUIVALENT to existence of one finite physical cut-star bad core
   carrying genuine selected eligible original names and complete
   next-cut ordinary L types.

The third assertion is the preceding Track D selected-stage
equivalence applied to P, with P.hRepresented and P.hNoI2; the
first two assertions supply the proof that the selected-stage test
is indeed the FULL pre-cut physical closure test. No additional
finite-source representation hypothesis is smuggled in.

This result is specialized to one chosen genuine finite AlgorithmRun,
not arbitrary diagram/diary occurrences or the infinite resolved
construction. In particular it does not prove that the active
macrodiary branches alone encode auxiliary cut-star sources.

## Hostile audit

1. Distinguish the subset inclusion Selected(v) -> represented(v)
   from the exact equality P.Full(v) <-> represented(v).
2. Distinguish name-level exactness from node-level completeness:
   P.Full exactness says nothing about a node omitted from the
   maintained original pool without the separate hX/closure invariant.
3. The pre-cut closure uses Run.I(p+1), not Run.I 0; the latter appears
   ONLY in the fixed original-name universe hStageOriginals.
4. The selected source may contain auxiliary originals, not just
   selected active diary branches.
5. no-(I2) is applied to the same physical Z and cut; no separate
   assumption of no-(I1) is needed for corrected B3 iff.
6. The actual run's hX original-prefix hypothesis is substantive;
   omitting it invalidates the full-node exhaustiveness claim.
7. The theorem is conditional on cut<top and p<N. A run top seed
   is not needed for the source representation itself.
8. The underlying finite L-only bad core has no auxiliary E, and
   arbitrary future--future edges are not physical H edges.
9. The source nonemptiness is represented in the bad-core condition;
   an empty physical cut-star source still passes corrected B3.
10. The equivalence is with failure of the TRUE full closure's
    corrected B3, not with loss in the selected-front graph-age
    F_before vs F_after. That remains an entirely separate
    fixed-source relative-realization/fidelity obligation.
11. No common labelled inverse-source orbit or exact BRD degree is
    inferred across occurrences.
12. The Lean specialization must name both existing Track B
    completeness theorems and the new Track D bidirectional B3
    theorem, and pass a fresh exact-head standard-only axiom audit.
    Do not rework verified old proof bodies or edit black manuscript.

## Implementation

Import Kk.B3ActualRunFullSourceCertification and
Kk.B3PhysicalBadCoreIff. State the three-way result as ONE theorem
over the exact same P. Apply the verified Track B exactness and
pool-exhaustiveness theorems and Track D iff with P fields.
Register one strict named transitive axiom report in an isolated
workflow, not in the central aggregator before CI.
