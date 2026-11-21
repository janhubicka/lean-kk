# Track E E85 — bound the NUMBER of maximal old-Kpt-prefix obligations by |U| + oldTop + 1, independently of physical carrier N

**21 November 2026. English-first mathematical proof and 24 adversarial checks committed BEFORE Lean.**

## A genuine improvement over E71–E84

The E79 maximal-complete-old-socle frontier supplies at most ONE old-live complete Kpt prefix matching test per physical numerical-H+ original v∈Fin N. Thus a naive upper bound on the number of distinct maximal tests is N, the size of the chosen physical H+ carrier, which can be arbitrarily inflated by adding dummy numerical blocks. Such a carrier-dependent estimate is insufficient for a diary-uniform finite source budget.

But a physical original v can have a NONEMPTY E79 eligible-cut set S_v only if it actually represents a NEW-LIVE Kpt crossing at some OLD run source cut c. By E71's verified genuine stage-original representation, it then belongs to the ACTUAL stage original pool

    hStageOriginals(K,k,N,U,R.I(c+1)).

For c<oldTop, genuine AlgorithmRun selected-tail monotonicity gives R.I(c+1)⊆R.I(0). Hence v already belongs to the ONE FIXED FINAL OLD original stage pool

    V = hStageOriginals(K,k,N,U,R.I(0)).

Therefore the number of v with S_v nonempty is bounded by |V|, not N. More importantly, the verified AlgorithmRun level-set bounds say

    q∈R.I(0)  ⇒  0≤q≤oldTop.

As every stage original v outside U is selected at its LITERAL physical original address v.val∈R.I(0), there are at most oldTop+1 such additional original coordinates. Thus

    |{v : S_v nonempty}| ≤ |V| ≤ |U| + (oldTop+1).

This bound is independent of N once the old run's top and the cardinality of its genuine seed root-original pool U are fixed.

**Important:** This is NOT yet a bound by the ABSTRACT DIARY alone. A separate theorem must control |U| and oldTop in terms of the diary across the resolved-Q construction and different occurrences; E85 does not construct a common labelled inverse-source orbit.

## Formal definitions

Take one true normalized Kpt family, one actual numerical-H+ structure A=finiteNumericH(K,k,N) avoiding family, a finite root-original set U⊆Fin N, old genuine AlgorithmRun R on arbitrary seed X with top h, and ANY candidate enlarged seed set Y. No new AlgorithmRun is needed. Let Allowed⊆Nat be an arbitrary source-cut subset (possibly disconnected).

Use E79's TRUE finite original support `kpt_actual_original_socle_allowed_cuts family K k N hAvoid U X Y h R Allowed v`. Its members are exactly OLD-BORING cuts c<h in Allowed where v belongs to the true physical stage original pool at R.I(c+1) and represents SOME new-live crossing z of closure_(R.I(c+1))(Y).

Define

    Need = {v∈Fin N : (E79 eligible old-socle cut set of v).Nonempty}.

This is a true Finset by classical finite decidability of its finite membership predicate. It does not enumerate Kpt meets/parameters and may include physically indexed original nodes that themselves are not live.

## E85.1 — stage pool monotonicity

For arbitrary original-stage level sets I⊆J,

    hStageOriginals(K,k,N,U,I) ⊆
    hStageOriginals(K,k,N,U,J).

Proof: unfold the exact finite original-pool definition. Membership means v∈U or v.val∈I and A.freeLevel(v)>0. In the latter case inclusion I⊆J preserves membership. No assumption about graphical source selected age or physical Kpt node closure is made.

## E85.2 — only FINAL old stage originals can need a test

Take v∈Need and choose any c in its nonempty eligible cut set S_v. E79's exact membership theorem provides c<h and v∈hStageOriginals(K,k,N,U,R.I(c+1)). From the verified genuine old AlgorithmRun `R.I_eq_final_tail_of_run (c+1)` with c+1≤h, the level-set inclusion R.I(c+1)⊆R.I0 follows. Apply E85.1 to obtain v∈V.

Hence Need⊆V and Need.card≤V.card.

This does not claim v itself lies in the OLD source closure, nor that a maximal prefix witness exists. It only bounds which physical original NAME could require one.

## E85.3 — final stage cardinal bounded independently of N

Unfold V. Let T be the finite set of physical original addresses v∈Fin N with v.val∈R.I0 (dropping the positive-free cut condition, which only enlarges the set). Then

    V ⊆ U ∪ T
    |V| ≤ |U| + |T|.

The verified `R.I_mem_bounds 0 (0≤h)` shows for every v∈T that v.val≤h. Map each v∈T to the Nat v.val in Finset.range(h+1). It is injective because distinct `Fin N` have distinct values. The standard Mathlib finite-injection cardinal inequality yields

    |T| ≤ |range(h+1)| = h+1.

Consequently

    Need.card ≤ V.card ≤ U.card + (h+1).

This is an actual quantitative improvement over the crude ≤N bound. It is independent of N for fixed |U| and h, and does not require Y to be a literal bare new root or an actual target AlgorithmRun.

The +1 is intentional: a genuine AlgorithmRun's selected-level set includes its top h (verified topI), so an assumed strict bound q<h would be wrong. At h=0, the estimate |U|+1 is safe.

## Application to E80/E84

E80 and E84 require one OLD Kpt prefix witness at max S_v for each v with S_v nonempty. By E85, at most |U|+h+1 such different maximal-prefix certificates are needed over ALL allowed cut classes combined. This bound does not grow just because the numerical-H+ carrier N is padded with additional physical originals not selected in the OLD run or among U.

This is the first bound in this E68–E84 line that removes explicit dependence on the NEW physical carrier size. To turn it into the desired diary-uniform exception/source budget, one must still relate genuine OLD source scan top h and genuine root pool size |U| to the fixed diary, and prove the existence of the maximal old-prefix witnesses. The common labelled inverse-source orbit remains another independent obligation.

## Hostile checks (24)

1. Need tests ONLY original v with nonempty E79 true eligible crossing support; not all Fin N coordinates.
2. E79 membership includes genuine old-boringness, stage pool inclusion, true new-live crossing source and Allowed.
3. No new AlgorithmRun on Y is assumed.
4. Old run R must be genuine for its selected-tail identity.
5. Cut c<h ensures c+1≤h, needed for R.I_eq_final_tail_of_run.
6. Selected level-set inclusion is DOWNWARD stage pool membership inclusion: R.I(c+1)⊆R.I0.
7. Actual hStageOriginals requires physical original v.val∈I and positive free E-level, not just arbitrary original-Q graph membership.
8. Root originals U remain present regardless of selected tail.
9. The FINAL old stage pool V is computed with the OLD R.I0, not a guessed new selected tail.
10. Need⊆V does NOT imply needed v is an OLD-LIVE Kpt closure node.
11. The candidate Y may introduce new meets/parameters; they are represented by final OLD stage original names because the closure uses OLD selected levels and genuine common physical pool in the E79 definition.
12. The crude N-bound holds but is not the quantitative endpoint.
13. The set T used for counting drops positive free-level eligibility, making it an overapproximation.
14. Old selected-level bounds are inclusive q≤h: top h is deliberately retained.
15. The map v↦v.val into Nat is injective on Fin N.
16. Every selected physical original address v.val∈R.I0 belongs to [0,h], so |T|≤h+1 even if N≫h.
17. Cardinal union inequality gives |V|≤|U|+|T|; overlap only improves the bound.
18. No assumption that U and selected originals are disjoint.
19. Allowed can have arbitrary gaps or mix isolated dummy and odd safe cuts.
20. A physical original representing multiple candidate Kpt nodes still causes only one maximal prefix test in Need.
21. A new source node represented by multiple physical originals may generate more than one test, but all are counted in V.
22. The bound controls the NUMBER of distinct maximal test OBLIGATIONS, not the NUMBER or HEIGHT of actual bad cuts when witnesses fail.
23. Without uniform bounds on h and |U| by diary, the theorem does NOT yet prove any diary-uniform bound.
24. No actual old-prefix existence, common labelled inverse-source orbit, arbitrary-occurrence coordinate normalization, upper/lower BRD equality or removal of K4 auxiliary q2/E cuts is asserted.

## Formalization gate

Create an independent standalone Lean module importing merged E79 and the existing genuine AlgorithmRun selected-level API. Prove: (1) hStageOriginals monotone in selected levels, (2) Need⊆V and its cardinality bound, and (3) the exact `Need.card≤U.card+(oldTop+1)` original-coordinate budget. Use Mathlib `Finset.card_le_card_of_injOn` for v.val's injection into `Finset.range(oldTop+1)` and `R.I_mem_bounds` for inclusive top. English committed BEFORE Lean, strict qualified named standard-only `#print axioms` reports with negative parser self-test, independent direct and full Lake builds. Frozen black manuscript unchanged; no global diary-uniform validation marker until the additional geometric/orbit gates are proved.
