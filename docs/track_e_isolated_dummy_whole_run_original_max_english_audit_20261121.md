# Track E E82 — whole genuine Kpt run through isolated original-Q dummy cuts with NO zero-stage hypothesis

**21 November 2026. English proof and 20 hostile adversarial checks committed BEFORE Lean.**

## Source and precise improvement

E80 (#425, already Lean-verified/merged) constructs an actual synchronized AlgorithmRun on Y=X∪{O_new} retaining the OLD actual `R.I` and entire monoid-valued `R.F`. It divides OLD-BORING cuts into allowed positive even-real ZERO-column stages and explicitly remaining cuts. For each allowed old-boring stage it needs only one maximal COMPLETE OLD Kpt-prefix witness per active physical original, thanks to E79.

E81 (source branch/PR #429) proves that at any genuine lower-real H+ position c=hPosition(k,idx,g) with g<k and c<N, if original-Q base idx is literally ISOLATED (`∀j, E idx j=false`), then the ordinary numerical-H+ L cut column is zero for **EVERY eligible physical original**, not merely a selected graph-age shadow or pre-cut stage pool. Its dedicated source acceptance must be independently checked before formalizing the E82 composition.

This note combines those results: for isolated original-Q dummy base cuts, the ZERO-column premise in E80 is automatic. The one maximal OLD-Kpt-prefix witness per physical original remains the substantial geometric condition.

## Exact theorem

Fix one actual finite numerical-H+ original-Q model A from a symmetric graph E, a finite root original pool U, an old genuine normalized Kpt AlgorithmRun R on represented seed set X, and ONE new complete physical original O_new with original coordinate newV∈U. The new INITIAL seed set is precisely Y=X∪{O_new}. Assume the ambient A avoids the normalized forbidden family.

Take any Set Allowed of literal old-range source cuts, perhaps disconnected. The sole allowed-cut classification hypothesis is:

    for every c<oldTop in Allowed,
      ∃ idx g : Nat,
         c = hPosition(k,idx,g),
         0 < c,
         g < k,
         c < N,
         and ∀ j : Nat, E idx j = false.

Thus Allowed consists ONLY of positive lower-real cuts at genuinely isolated old-Q dummy bases. No finite auxiliary source enumeration, diary Plan equality, new Y run, or full-stage zero ordinary-L predicate is assumed.

For each physical original v∈Fin N, define S_v to be E79's finite set of Allowed genuinely OLD-BORING cuts at which v represents some actual NEW-LIVE crossing Kpt source z≤O_v. Require one OLD-LIVE COMPLETE Kpt prefix match for O_v at max S_v, if S_v is nonempty.

For all genuinely old-boring cuts c<oldTop outside Allowed, require full physical NewRootNoNoveltyAtCut with the candidate NEW closure evaluated on the OLD run's selected tail `R.I(c+1)`.

**Conclusion:** There exists a genuine AlgorithmRun RY on Y of the SAME top with

    RY.I=R.I and RY.F=R.F

as literal functions (including the entire monoid-valued F, not only the selected I).

## Proof

1. For each Allowed c<h, choose idx,g with the stipulated actual positive lower-real coordinate, carrier bound and isolation of idx.
2. Apply the verified E81 all-eligible zero original L lemma: every v∈Fin N with `c+1≤A.freeLevel(v)` has `A.L.binary c v 0=false`, independent of U or the actual old source-tail J.
3. Restrict that universal conclusion to `hStageOriginals(...,U,R.I(c+1))`. This establishes EXACTLY E80's `KptActualPositiveEvenRealZeroStage` predicate; no extra zero-column condition is needed.
4. Apply E80 with the stipulated maximal OLD-Kpt-prefix original certificates and outside-Allowed physical no-novelty conditions. E80 uses E79 to move each physical old prefix witness downward, E77 to eliminate seed/generated I1 and compare full L+/E upper pairs at zero columns, and G365 to build the actual new AlgorithmRun preserving both I and TOTAL F.

## Why the original-Q dummy hypothesis is meaningful

Track D's genuine resolved-Q roles include ISOLATED dummy bases. If the intended resolved original-Q construction truly has `role idx=dummy` and the verified chronological Q axioms force `∀j,E idx j=false`, then these base cuts can be put into Allowed without a separate induction on the proposed stage Plan. But the theorem does NOT infer that every omitted cut is dummy or zero-column, and does not put selected coding or auxiliary-block cuts into Allowed without proof.

The remaining OLD PREFIX witness is not automatic from isolation: the new physical original may have a complete dependent E/L old prefix not yet represented by an old-live Kpt source. This must be established by the resolved-diaries' actual original-prefix construction, not only by ordinary Q graph adjacency.

## Hostile checks (20)

1. The outgoing-isolation property concerns the ACTUAL original-Q Boolean graph E, not auxiliary Kpt E.
2. No assumed symmetry of Kpt auxiliary directed E.
3. Original Q graph E symmetry is supplied separately for E77/E80, not needed for E81's zero column alone.
4. Each Allowed c is an actual lower-real H+ address, g<k, c<N and c>0.
5. The source carrier bound c<N cannot be silently removed.
6. The new bare original has genuine numerical-H+ original coordinate newV∈U.
7. Old X may include genuine dependent seed nodes; no all-old-seeds-are-originals shortcut.
8. New initial seeds are X∪{O_new}, not inherited old parameter closure or all-ancestor prefixes.
9. Every candidate NEW full source is computed from the OLD R.I(c+1) tail.
10. E81 zeros all eligible physical original coordinates, so in particular the FULL stage originals, not merely selected graph-age names.
11. No equality of planned retained levels to the old actual run's selected-tail set is inferred.
12. The maximal prefix source witness is an actual OLD-LIVE Kpt node with the SAME COMPLETE old ancestor.
13. E79's eligible cut sets may have gaps; no convexity of Allowed or boring stages is assumed.
14. Every source-cut outside Allowed is NOT automatically quiet; a separate physical no-novelty condition remains.
15. K4 q2/E cuts 10/22 are only covered when their exact physical classes and prefix witnesses satisfy the assumptions.
16. I2 forks, auxiliary meets and E-dependent parameters are included in E77/E80's actual physical relation.
17. No target Y AlgorithmRun appears in hypotheses; whole-run existence is the conclusion.
18. Literal RY.F equality is the total monoid-valued function, not a selected-level shadow or arbitrary-factor equality.
19. N may grow with the finite H+ stage; at most N maximal tests is not a uniform diary bound.
20. No cross-occurrence normalization, common labelled inverse-source monoid orbit or BRD upper/sharp equality is proved.

## Lean validation

After E81 standalone exact-head CI passes and merges, formalize E82 as a standalone theorem importing E80 and E81. First derive E80's zero-stage predicate at every Allowed cut by supplying the E81 universal original-column theorem. Then apply E80 unchanged, preserving the old actual R.I tails and its other-cut no-novelty hypothesis. Run strict named standard-only transitive-axiom gate with negative parser self-test, standalone and independent full Lake CI. Keep the manuscript black frozen and the global bound/orbit markers pending.

## Exact verified dependency checkpoint (21 November, before E82 Lean source)

* E80 [PR #425](https://github.com/janhubicka/lean-kk/pull/425), exact head `43251a6a3512a814596057f8c53f26196ed1e460`, dedicated strict two-name [run #44919565852](https://github.com/janhubicka/lean-kk/actions/runs/44919565852) **PASS**, independent whole Lean [run #44919565741](https://github.com/janhubicka/lean-kk/actions/runs/44919565741) **PASS**, merged.
* E81 [PR #429](https://github.com/janhubicka/lean-kk/pull/429), exact head `8538abc23562902be5b61179975b2b226c9b4b7a`, dedicated strict two-name [run #44919912217](https://github.com/janhubicka/lean-kk/actions/runs/44919912217) **PASS**, independent whole Lean [run #44919912133](https://github.com/janhubicka/lean-kk/actions/runs/44919912133) **PASS**, merged.

Both E80/E81 are verified at these exact source heads before the E82 formal composition. E82 itself still requires independent exact-head direct compilation, named strict standard-only axiom reports, and full repository build. No global manuscript marker is promoted by merely writing the composition.
