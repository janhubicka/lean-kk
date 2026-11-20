# Track E E74 — physical stage-original prefix cover implies ALL candidate old-Kpt socle coverage

**19 November 2026. English proof and 20 adversarial checks committed BEFORE Lean.**

## The remaining E72 hypothesis and its finite-stage normalization

Merged E72 shows: in one finite numerical-H+ stage with all eligible ordinary-L cut bits zero and symmetric ambient L, equality of the full OLD Kpt ancestor of each new-live crossing node z with that of SOME actual old-live Kpt node already forces equality of its entire dependent old/upper L+/E crossing pair. That is mathematically strong but still quantifies over all auxiliary Kpt meet and parameter nodes in the new closure.

The verified genuine stage-normal-form theorem `finiteNumericH_stage_closure_represented_by_stage_originals` provides the missing normalization. Every candidate Kpt closure source z is BELOW a genuine full Kpt original O_v for v in the actual pre-cut original stage pool. If z crosses cut c, its old Kpt ancestor at c is literally the old ancestor of O_v. Therefore we need only match at most N ORIGINAL old-source prefixes, rather than all actual Kpt sources.

## Exact setup

Fix family, a genuine finite numerical-H+ structure A=finiteNumericH(K,k,N) avoiding it, the full original root pool U⊆Fin N, one genuine old AlgorithmRun R on a seed set X, and candidate enlarged seed set Y represented by U. Use the old selected source levels J=R.I(c+1) for both Zold=closure_J(X) and Znew=closure_J(Y), where c is a genuine source coordinate.

For v∈Fin N, say it is **active as a candidate stage representative at c** if

    v∈hStageOriginals(K,k,N,U,J)
    AND ∃z∈Znew with c<lev(z) and z≤O_v.

The actual original O_v need NOT itself be in Znew. Its role is to represent the old and upper Kpt prefix of a genuinely live z.

Assume only the following finite original-coordinate **prefix coverage**:

    For every candidate-active representative v,
    ∃w∈Zold with c<lev(w), c<lev(O_v) and
       ancestor_c(O_v)=ancestor_c(w)

as an equality of ACTUAL Kpt nodes, with full L+/E history. The w may depend on v. Original-name injection, membership of O_v in Zold, and equality of upper types are NOT assumed.

## E74.1 — stage-original prefix matching transfers to all new-live Kpt sources

Fix any z∈Znew crossing c. The true original-stage representation theorem gives some v in the ACTUAL stage pool such that z≤O_v. Hence v is active and the finite original prefix hypothesis supplies w∈Zold crossing c with ancestor_c(O_v)=ancestor_c(w).

Because z≤O_v and c<lev(z), the LevelTree uniqueness of ancestors gives

    ancestor_c(z)=ancestor_c(O_v).

By transitivity, ancestor_c(z)=ancestor_c(w). This supplies **exactly** E72's full old-Kpt socle coverage hypothesis for EVERY new-live crossing node, without enumerating the auxiliary closure and without assuming a new run. This direction supplies a sufficient test; the reverse implication is also valid **for precisely the active-original condition stated here**. Indeed, each active v represents a crossing z with the same complete old Kpt ancestor, so an old-socle witness for z also witnesses v. E78 records the full equivalence and its independent Lean acceptance gate. The physical test universe has size at most N in this finite stage, but N is not a diary bound.

## E74.2 — complete dependent crossing coverage at zero-column cuts

Specialize to signature (db=1,du=0,dd=1), symmetric ambient ordinary-L table and zero L(c,v) for ALL eligible physical originals in the actual pre-cut stage pool. By E74.1 we have E72's full old-socle coverage. The merged E72 theorem then yields

    FullPhysicalClosureCrossing(family,Znew,c)
        ⊆ FullPhysicalClosureCrossing(family,Zold,c).

The old/new full raw type includes dependent auxiliary E and both negative ordinary L directions. The result works with all I2 forks, since each source crossing pair has a single old physical witness. The upper type is now obtained through the verified six-field zero-column lemma rather than assumed as a mysterious independent geometric parameter.

## Why this improves the actual KK-free application

At a zero ordinary-L stage, the missing entire Kpt crossing check has been reduced to matching the FULL OLD partial type of each genuinely active stage ORIGINAL, not the complete upper type or the entire auxiliary closure. The original type can be computed directly from the actual numerical-H+ columns, potentially permitting the resolved-Q dummy/selected/auxiliary role analysis from Track D. This is the next real geometry gate.

It does not establish that those original prefix matches exist for the resolved diary. It also does not remove I1 terminals at arbitrary cuts; Track D's positive even-real no-I1 result is a separate application, provided seed absence holds. Uniform diary source bounds, cross-occurrence cut normalization, outgoing labelled monoid orbits and BRD equality are still open.

## Hostile checks (20)

1. Only ONE genuine OLD AlgorithmRun R is assumed; new closure uses R.I(c+1).
2. The original root pool U actually represents Y, not a selected graph shadow.
3. The representative v lies in the **true STAGE** pool, not the final R.I 0 pool.
4. The original O_v may not be live; do NOT assume its membership in either closure.
5. Active-original condition explicitly includes some crossing new-live z≤O_v.
6. A physical original can represent multiple z; the same old prefix test covers all their old Kpt ancestors at c.
7. Several physical originals can represent one z; no canonical choice or injection is required.
8. The old witness w must be an actual OLD-LIVE source in closure_J(X).
9. w must really cross c, not merely have an ordinary-L type in an abstract graph-age shadow.
10. The old ancestor equality is equality of complete Kpt nodes, including E and negative L.
11. `LevelTree.eq_ancestor_of_le` verifies restriction of a physical full original to a represented prefix.
12. No constraints on h>c are needed for the local geometric lemma, except using R's genuine level-tail function as defined.
13. The stage pool is at most N originals for this particular finite H+ carrier, but N is NOT uniformly controlled by diary.
14. **Adversarial correction (20 November):** for a truly ACTIVE original v representing a crossing z, the complete old ancestors coincide, so source-level old-socle coverage also gives original-prefix coverage. The two criteria are equivalent under actual stage representation (E78 English proof); an original not representing any crossing z is vacuous.
15. E74.2 requires whole-stage zero ordinary L, not merely zero selected-front L.
16. Physical ordinary L symmetry includes fake H coordinates; E remains directed.
17. E72 supplies full L+/E upper matching from complete old source type plus zero L, not from bare graph adjacency.
18. No I2 uniqueness is assumed; competing pairs are separately covered.
19. Cut-level I1 terminals are separate and not handled by a crossing original ancestor test.
20. K4 auxiliary E/q2 source cuts 10 and 22 and the global missing source-orbit/BRD gates remain.

## Validation gate

Write an independent Lean module importing verified true stage-original representation and E72. Prove exact per-original representative-active membership if introduced, the general full Kpt old-socle-transfer theorem (arbitrary signature), and the zero-column complete-crossing corollary. Run direct Lake compilation, a strict named standard-only transitive-axiom gate with negative parser self-test, and independent full project build. Keep manuscript frozen black text unchanged and source-only PR draft until exact-head CI green.
