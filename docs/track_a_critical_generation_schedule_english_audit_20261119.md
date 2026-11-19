# Track A — finite genuine Henson raw critical-generation schedule

19 November 2026. English mathematical proof and adversarial audit of the Lean module `Kk/PartialNumericCriticalGenerations.lean`. The audit was committed after the initial source file; the mathematical dependencies were already proved in the earlier English audits.

## Definition and exact interval theorem

Fix an actual symmetric loopless original E avoiding the normalized `hensonForbiddenFamily ell hell`, current original b, numerical height k, carrier M, and GIVEN later original top names j(t)>b. Let U range over ALL admissible NONEMPTY supports (not only singleton supports). Put

- P_U = {i<b : every E(i,j(t)) is true for t in U};
- S_U = {i in P_U : E(i,b) is true};
- p_U = cap_E(P_U), c_U = cap_E(S_U);
- critical(U) iff b is positively linked to ALL j(t) in U and c_U=p_U.

Define the finite original-derived event schedule

    C(E,b,j) = {p_U : U admissible and critical(U)}.

**Theorem.** At physical partial cuts g<=h<=k in the SAME original b block, the complete literal ordinary-L raw support functions differ precisely when C meets the half-open interval [g,h):

    Raw_h != Raw_g  <->  exists p in C, g<=p<h.

**Proof.** The previously derived *whole raw-function change iff named support event* says that Raw_h differs from Raw_g exactly when some U is critical and g<=p_U<h. By the image definition of C, this is exactly the stated interval criterion. No additional physical assumption is inserted: the earlier whole-function theorem already establishes that the source is the complete numbered numerical-H binary-L prefix with all odd dummy coordinates.

The raw age is constant along a generation interval iff that interval contains no member of C. Hence all raw changes are localized to finitely many critical generations. By the two-original forbidden-clique argument, every p in C obeys p+2<ell; thus for ell>=2 all possible event indices are <ell-2.

## Hostile audit

1. C is an image of a FINITE set of supports, so it is finite even if original E is a total Nat-to-Nat Bool graph.
2. Critical supports can share the same p; C is a set of *event indices*, not a count of supports.
3. C is defined independently of the current numerical cut g, height k and Boolean carrier M; nevertheless the interval theorem only applies to actual partial cuts within g<=h<=k, and only to the same given future tops j.
4. No raw event exists at a *single* cut without comparing before/after; our convention is that p indexes the transition p -> p+1, so the half-open interval [g,h) is exact.
5. A critical p>=k is harmless: it has no completed partial step before top within the allowed interval. The schedule C need not be artificially truncated to k.
6. Only nonempty admissible supports are used. Empty support would destroy the indispensable later original j(t) in the forbidden-clique argument.
7. Even if C is empty, we conclude ordinary-L *raw* constancy, not Kpt interestingness or B3 preservation.
8. Different supports can activate at different generations; a given support activates at most once.
9. A raw event may be canonically redundant; C does NOT directly count canonical covers.
10. Complete original E is fixed. Comparing different successor-selected substructures, changing j, or reindexing Kpt nodes requires additional transport.
11. Auxiliary full partial L+/E old/upper crossings, I1 terminals, I2 meets, and I3 skip constraints may remain nontrivial after all ordinary critical generations.
12. This result should NOT be used to mark the whole-H block boring unless all auxiliary exact-source profiles are controlled independently.
13. No claim of a BRD upper or lower bound follows, and no reliance is placed on an unvalidated diary definition.

## Lean acceptance

New endpoints:

- `Kk.mem_trackACriticalGenerations_iff`;
- `Kk.trackA_henson_raw_change_iff_critical_generation`.

They should be compiled with their imported eleven theorem endpoints from `Kk/PartialNumericForbiddenSharpStability.lean`. Check the exact qualified axiom reports with the existing strict parser, and run `lake build`. These are source-level submissions, **not verified Lean results**, unless a corresponding exact-head successful workflow is observed. Do not promote the frozen manuscript validation marks. Main body editing is deferred until that gate passes.

## Next bridge to the dependent source

At each cut cut, add the actual Kpt terminal-presence flag, the full physical old/upper L+/E crossing relation (not an L-only projection), and the I3 skip check. Existing Track E/G modules formalize these physical interfaces for finite indexed sources. The ordinary C schedule is only one part of this combined record. To show an off-plan level boring, one must still prove the remaining dependent Kpt components absent/covered; emptiness of C is insufficient.

## Sharp upper bound on number of raw event generations

For each p in the critical schedule C, the membership lemma supplies a
nonempty critical support U satisfying p=cap_E(P_U) and c_U=p.
Choose any named top j(t) with t in U. Let S_U be the linked original
pool. Its actual maximum clique of size p, together with the distinct
originals b,j(t), is a directed complete original clique of size p+2.
Genuine forbidden-family avoidance gives p+2<ell, hence p<ell-2.

Therefore

    C subset {0,...,ell-3},
    |C| <= ell-2.

The bound is independent of the number of target sorts and of the
numerical gadget height. It counts **different raw transition indices**,
not the number of critical supports and not the number of canonical
covers or full Kpt interesting levels. It also holds for ell=2
(vacuously: C is empty because a critical support would produce an edge).

New Lean source endpoints:
- `trackA_henson_critical_generation_lt_ell_sub_two`;
- `trackA_henson_critical_generation_card_le`.

Both are source-level proofs pending an exact-head Lean build.
