# Track E E72 — physical zero-column source-socle coverage forces COMPLETE L+/E crossing coverage

**19 November 2026. English FIRST; adversarial audit before the Lean implementation.**

## Critical distinction

The remaining numerical-H+ difficulty is complete dependent old/upper L+/E crossing matching at old-boring physical cuts. The original graph-age shadow alone is insufficient, and the actual K4 E/q2 cuts (10 and 22) demonstrate that auxiliary Kpt nodes cannot be discarded.

Track D has now verified a **genuine full-dependent next-column uniqueness** theorem:
`full_zero_ordinary_cut_column_determines_next_type`. In one actual `EnumeratedPartialStructure 1 0 1` with symmetric ordinary L, two FULL physical original types eligible to cross cut c, whose complete old `PartialTypeWithE c` values agree and whose ordinary L cut bits are both false, have the SAME complete new type at c+1. The auxiliary E bit and its reverse are included (forced by free-level eligibility); they are not invented for a pure graph witness.

This permits a simpler crossing criterion than E69/E71 at **zero-column** candidate stages: require a match of the old complete Kpt *socle at c* from an actual old-live source node, rather than matching its unknown full upper successor type.

## Data

Fix a normalized forbidden family of signature (db=1,du=0,dd=1), an actual finite numerical-H+ structure A=finiteNumericH(K,k,N) avoiding family, with symmetric entire ordinary L table (Track D verifies this for an original symmetric graph), and a finite original pool U⊆Fin N. Let X⊆Y be Kpt seed sets, with Y inside the genuine ambient prefix pool `ambientPrefixPool(family,A,hAvoid,U)`. Let R be ONE actual old AlgorithmRun on X of top h. For c<h let

    Zold(c) = closure_(R.I(c+1))(X)
    Znew(c) = closure_(R.I(c+1))(Y).

These use the SAME selected level tail of the old run; no new AlgorithmRun on Y is assumed.

Define a **zero stage at c** to mean

    for each actual v in hStageOriginals(K,k,N,U,R.I(c+1)),
    if c+1<=A.freeLevel(v), then A.L.binary(c,v,0)=false.

This tests the COMPLETE physical stage original pool, not just the selected-front marks, and includes actual eligible auxiliary generators.

Define **full old-Kpt socle coverage** at c:

    for each z∈Znew(c) with c<lev(z),
    exists w∈Zold(c) with c<lev(w)
      and ancestor_c(z)=ancestor_c(w)

where ancestor_c equality means literal equality of complete Kpt nodes, including all old auxiliary E and negative L data. This is deliberately stronger than ordinary old L-only type equality; replacing it by positive adjacency masks is INVALID.

## E72.1 — zero-column socle transport to one complete old/upper physical pair

Fix one new-live crossing z and one old-live crossing w with matching complete old Kpt ancestor at c. By the verified actual stage-normal-form theorem for **both seed sets**, choose real original representatives v,u in the SAME stage pool with

    z<=O_v   and   w<=O_u.

Since both nodes cross c, c+1<=lev(z),lev(w), hence c+1<=freeLevel(v),freeLevel(u). The zero-stage hypothesis gives the complete ordinary L cut bit 0 for BOTH physical originals.

By restriction of original ancestors, ancestor_c(z)=ancestor_c(w) implies

    A.partialTypeAt(c,v) = A.partialTypeAt(c,u)

as COMPLETE dependent L+/E raw types, not only ordinary L records. The verified Track D full-zero-next theorem then gives

    A.partialTypeAt(c+1,v) = A.partialTypeAt(c+1,u).

The verified physical-original ancestor identity lifts this to

    ancestor_(c+1)(z) = ancestor_(c+1)(w).

Thus w is a genuine OLD physical witness for the very same COMPLETE upper ancestor of z. Every complete old/upper crossing pair contributed by z is already in the old pre-cut closure. NO no-I2 assumption is made: each possible z is processed independently.

**Important scope:** original representatives need not themselves be members of Zold or Znew; their role is to compute the actual COMPLETE upper type. Only w is the actual old-live crossing witness.

## E72.2 — the local full physical crossing inclusion

Under full old-Kpt socle coverage and the complete zero-stage condition,

    FullPhysicalClosureCrossing(family,Znew(c),c)
      ⊆ FullPhysicalClosureCrossing(family,Zold(c),c).

Proof: for each pair choose its actual new source z, take the old socle witness w, apply E72.1, then reconstitute the same pair with w. This is true even with I2 forks, without choosing a prescribed upper-type function, source enumeration, outgoing inverse-source map or new AlgorithmRun.

## E72.3 — optional terminal handling and geometric application

**Full physical no-novelty** at cut c additionally requires there be no NEW terminal without an OLD terminal. The ZERO-column hypothesis alone DOES NOT exclude terminals at arbitrary cuts. For positive even real numeric-H positions, Track D PR #389 separately proves that no I1 terminal exists when there are no initial seeds ending there, the COMPLETE original stage has zero eligible L bits, and symmetry holds. This is the correct route to discharge the terminal condition at such cuts (once that theorem has passed CI and merged), not a fake conversion of terminals into crossing pairs.

For an eventual old-run transport theorem, split genuinely old-boring cuts into (a) zero-column cuts with full old-Kpt socle coverage and I1 terminal check, (b) finitely controlled nonzero/auxiliary microevents requiring separate complete physical checking. Do NOT assert that every physical cut belongs to class (a) or that the exceptional set is diary-uniformly bounded.

## Adversarial checks (23)

1. **One** genuine old run; no target run is assumed.
2. Actual full Kpt pre-cut closure at R.I(c+1) for X and Y, not selected graph shadows.
3. X⊆Y is needed for real source monotonicity; a separate Y-run is never used.
4. Y⊆ambientPrefixPool of a single genuine finite numerical-H+ structure.
5. U is a finite original-coordinate root pool; both old and new sources share its complete stage index.
6. Stage uses R.I(c+1), NOT R.I(0).
7. Stage zero tests every eligible original including unselected auxiliary generators, not only selected coded copies.
8. The physical ordinary-L table must be symmetric on ALL numerical-H coordinates, including fakes.
9. Auxiliary E is directed and is NOT assumed symmetric.
10. Both original free levels are at least c+1, derived from z≤O_v and w≤O_u plus crossing.
11. A positive E-free-level real original cannot be guessed merely from its original graph Q role.
12. FULL ancestor_c(z)=ancestor_c(w) is needed, not ordinary L-only old socle.
13. Ancestor equality is literal equality in the same normalized Kpt tree.
14. For each source z, the old witness w may depend on z; one-to-one names are not claimed.
15. The original representatives v,u need not lie in the closure sets themselves.
16. I2 forks cause no issue because matching is pair-by-pair.
17. Neither the new Kpt source cardinality nor its injection from old matters.
18. This is LOCAL to one true source cut; no unrelated occurrence cut reindexing.
19. Terminal-I1 is separate: c=lev(z) has no upper crossing ancestor.
20. At even real cuts the Track D no-I1 lemma has additional explicit seed/no-even and zero-stage hypotheses.
21. K4 auxiliary E/q2 cuts 10 and 22 remain visible, not blanket-allowed.
22. Socle coverage is itself a genuine open geometric task for the resolved numerical-H+ schedule.
23. No diary-uniform original source carrier, common labelled inverse monoid orbit, global BRD upper or sharp counts are proved.

## Lean plan

Prove E72.1 as an actual stage-represented same-old-socle ⇒ same-upper ancestor theorem; E72.2 as exact full physical crossing inclusion; and optionally its conditional no-novelty corollary with a separate I1 hypothesis. Use verified Track D original stage-representation and exact six-field next-column uniqueness, preserving all dependent E and negative ordinary L bits. Record named standard-only axiom reports, standalone and independent full Lake builds. Keep manuscript black prose unchanged, existing validation markers unpromoted, and pending numerical-H+ geometry explicit.
