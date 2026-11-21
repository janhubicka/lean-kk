# Track E E80 — construct a whole synchronized Kpt run from maximal old-socle tests on zero-column cuts

**21 November 2026. English-first proof and adversarial audit, committed before Lean.**

## Target

Merged E77 proves that an OLD-BORING positive even-real cut in a genuine one-bare-root numerical-H+ extension is physically quiet when (Z) the COMPLETE physical stage-original ordinary-L column is zero, and (P) every active physical original has a complete old-Kpt prefix match. E79 shows that the OLD prefix condition (P) at a finite family of eligible cuts is equivalent to a SINGLE highest-cut old-source witness per physical original, even if the eligible cuts have gaps. G365 builds a genuine new AlgorithmRun with the entire old I and TOTAL F whenever every OLD-BORING cut is physically quiet.

E80 composes these verified theorems, without postulating any target run and without hiding other cut classes or the geometric witnesses that remain unknown.

## Exact physical setup

Fix a normalized forbidden family of signature (db,du,dd)=(1,0,1), a symmetric original graph E, one actual finite numerical-H+ expansion `A=finiteNumericH(normalizedGraphModel E,k,N)` avoiding family, a genuine finite original-pool `U:Finset(Fin N)`, one OLD Kpt source seed set X represented in `ambientPrefixPool(family,A,hAvoid,U)`, and one TRUE old AlgorithmRun R on X of top h.

Take ONE new physical original `newV:Fin N` with `newV∈U` and the new INITIAL seed family

    Y = X ∪ { A.kptOriginal(family,hAvoid,newV) }.

The candidate NEW pre-cut source at c<h is defined using only the OLD run's selected levels:

    Znew(c) = closure_(R.I(c+1))(Y),
    Zold(c) = closure_(R.I(c+1))(X).

The new AlgorithmRun does not occur among the assumptions.

Let `Allowed : Set Nat` be any collection of source cuts, including possibly gaps, satisfying:

    for every c<h with c∈Allowed, there exist idx,g
      such that c=hPosition(k,idx,g)>0 and
      every v∈hStageOriginals(normalizedGraphModel E,k,N,U,R.I(c+1))
      with c+1≤A.freeLevel(v) has A.L.binary(c,v,0)=false.

Thus Allowed only contains ACTUAL positive even-real full-stage zero ordinary-L cuts. It need not contain all such cuts, nor all OLD-BORING cuts. We do not assume a proposed diary Plan is the actual selected-tail set.

For each v∈Fin N, use the E79 finite set `S_v` of genuinely OLD-BORING cuts c<h where v represents SOME actual NEW-LIVE crossing source node and c∈Allowed. The *maximal-prefix geometric certificate* is

    for every v with S_v nonempty, OldSocleCovered(O_v,max S_v).

Here OldSocleCovered means that an ACTUAL OLD pre-cut source w crosses max S_v and has the exact SAME complete old normalized Kpt ancestor as physical O_v, including directed E and negative ordinary L.

Finally, for each OLD-BORING c<h outside Allowed require:

    NewRootNoNoveltyAtCut(family,Zold(c),Znew(c),c).

This final assumption is **explicit**: omitted other cuts (including odd/fake E, nonzero ordinary-L, and exceptional K4 microevents) are not declared harmless or charged to a budget automatically.

## Theorem E80 — exact synchronized whole-run existence under partitioned certificates

Under the data and assumptions above, there exists a genuine AlgorithmRun RY on Y of the same top h with literal function equalities

    RY.I = R.I   and   RY.F = R.F.

The second equality is of the ENTIRE monoid-valued F function, not just selected cuts or the existence of accumulated boring factors.

### English proof

1. Since newV∈U and every old seed is in ambientPrefixPool U, E77's verified pool lemma gives Y⊆ambientPrefixPool U. Also X⊆Y by literal union.
2. Invoke verified G365 `kpt_transport_actualRun_of_boring_only_noNovelty` for R,X,Y. It suffices to supply physical no-novelty at every c<h that is genuinely OLD-BORING on the complete Zold(c).
3. Fix such c. If c∉Allowed, the explicit other-cut hypothesis supplies physical quietness, without changing any selected level or Kpt source coordinates.
4. If c∈Allowed, obtain actual idx,g with c=hPosition(k,idx,g)>0 and the complete stage-zero predicate (Z).
5. To discharge E77's active-original prefix condition (P), take any genuine active physical original v at cut c, with a witness new source z∈Znew(c) crossing c and z≤O_v. E79's application-facing theorem `kpt_actual_original_socle_covered_of_all_allowed_max` gives an ACTUAL old-live complete Kpt prefix witness at c, by transporting the maximal-source prefix witness for v DOWN to c. This uses only the OLD run and full Kpt ancestors; no upper L+/E matching is assumed.
6. Apply the merged E77 `finiteNumericH_old_boring_one_bare_root_even_real_noNovelty` to this cut c with (Z),(P). Its proof uses E76 to make the initial-Y-seed terminal condition automatic for a bare-root insertion at an old-boring positive even-real cut; Track D excludes generated I1 terminals at zero stages; E72 transfers the dependent upper L+/E paired crossing relation. Thus `NewRootNoNoveltyAtCut` holds at c.
7. The resulting ALL-OLD-BORING no-novelty premise for G365 produces a genuine RY with exactly the same I and entire F as R. The target run is a CONCLUSION only.

No finite auxiliary Kpt source-node enumeration is required. The number of nonempty `S_v` is at most N in this physical numerical-H+ stage, regardless of the number of eligible cuts or generated Kpt meet/parameter nodes.

## Adversarial audit (24 items)

1. There is exactly ONE input genuine AlgorithmRun, on X.
2. The actual new initial seeds are X∪{ONE complete physical original}, not `closure_I(X)` or all ancestors.
3. X may contain legitimate dependent seeds; no assumption that every old seed is an original.
4. The new original belongs to U, guaranteeing a common TRUE physical pool; no hidden enlargement of U.
5. Every candidate Znew(c) uses the OLD run's R.I(c+1), never a supposed Y-run tail.
6. G365 needs only OLD-BORING cuts, not new-boring cuts or all cuts.
7. Allowed may be arbitrary/disconnected; no convexity of its source cuts.
8. Every Allowed cut below h is positive and a REAL numerical-H position; odd/fake source cuts are not forced into the even-real theorem.
9. Every Allowed cut's ZERO test quantifies over ALL genuine eligible physical stage originals, not just selected original coding names.
10. A stage original v may not itself be NEW-LIVE; E79 tests only active originals representing an actual crossing z.
11. The eligibility set S_v includes c<h, genuine old-boringness, stage-original membership, actual NEW-LIVE crossing, and Allowed.
12. If S_v is empty there is no test for v; do not take a spurious max.
13. The maximal old-prefix witness is an actual OLD-LIVE Kpt source at max S_v, not a selected graph-age type.
14. E79 transports prefix equality DOWN, not UP; cut≤max S_v is the correct orientation.
15. One maximal prefix witness may be used at several lower cuts via closure monotonicity.
16. The old-Kpt ancestor includes full dependent E, both directed ordinary L bits and negative atoms.
17. No upper successor-type matching is claimed at nonzero cuts; E77 relies on zero ordinary-L uniqueness.
18. True I2 forks and generated auxiliary meets/parameters are included in E77's full crossing/I1 reasoning.
19. No blanket assumption that K4 E/q2 microcuts 10 or 22 are harmless; they must belong to Allowed only if the exact stage zero/real predicates hold.
20. Other old-boring cuts c∉Allowed are explicitly required to be physically quiet; this is NOT proved or disguised as a consequence.
21. G365 constructs literal total F equality, not uniqueness of F among arbitrary independently chosen new runs.
22. The bound “at most N maximal certificates” is stage-specific and does not imply uniform bounds by diary size.
23. No cross-occurrence coordinate normalization, assigned successor-character transport, common labelled inverse-source monoid orbit or sharp BRD is proved.
24. The theorem is conditional, and the actual resolved-Q stage must separately provide the maximal source-prefix witnesses and all outside-Allowed cut certificates.

## Formalization and validation gate

Create a standalone Lean module importing E79, E77, and G365; prove (a) an application-facing one-cut derived physical no-novelty theorem from the E79 maximal old-source prefix certificate and physical zero column; (b) the genuine whole-run construction with exactly old I and TOTAL F. Keep conditional hypotheses visible in the signatures. Compile directly with Lake and strict named standard-only axiom reports (plus parser negative self-test), independently run full project Lean, and preserve black manuscript text/TODO decisions. Only after exact-head green add source-pinned BLUE marks to the olive manuscript.
