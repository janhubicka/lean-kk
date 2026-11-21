# Track E E81 — actual isolated-dummy original-Q bases give zero physical columns automatically

**21 November 2026. English-first mathematical proof and 21 hostile checks, committed before Lean.**

## Why this is substantial

The E80 whole-run theorem, currently under exact-head CI, requires two kinds of physical geometry: (1) an actual full-stage zero ordinary-L cut column at a chosen positive even-real cut, and (2) a complete OLD Kpt-prefix witness at one maximal eligible cut per physical original. The zero-column assumption is not automatic for arbitrary resolved-Q bases.

But for a truly ISOLATED original-Q dummy base idx, the first of these two hypotheses is a theorem of the actual numerical-H+ ordinary-L generator. The verified Track D source `Kk.TrackDZeroStageActualRunSkip` already uses the exact generator classification

    finiteNumericH_eligible_lower_cut_neighbour_is_higher

to prove a stronger fact in a different application: **ANY** eligible original v with a positive L(c,v) at the lower real source cut c=hPosition(k,idx,g), g<k and c<N, forces a TRUE base edge E(idx,j)=true to some later original-Q base j. If idx is isolated, that is impossible.

This fact applies to every actual physical original in the entire ambient numerical-H+ carrier, not just to original names of a selected Kpt source stage. Thus there is no possible hidden dependence on the proposed diary retained-set Plan or a selected graph-age shadow.

## E81.1 — isolated dummy zero-L lemma

Let E:Nat→Nat→Bool be any original Q graph Boolean edge relation; we need no symmetry for the basic absence of the outgoing L bit. Fix finite numerical H+ model

    A = finiteNumericH(normalizedGraphModel E,k,N),

an original base idx, a lower generation g<k, a source cut c=hPosition(k,idx,g)<N, and assume

    for every j, E(idx,j)=false.

Then for EVERY physical original coordinate v:Fin N with

    c+1 ≤ A.freeLevel(v),

we have

    A.L.binary(c,v,0)=false.

**Proof.** Suppose instead the bit is true. The checked exact eligible-lower-cut neighbour classification provides a later original-Q address j and a real generation m satisfying E(idx,j)=true. This contradicts isolation of idx. We use the complete actual numerical-H+ generator, not a new defined auxiliary E or an ordinary-L selected shadow.

There is no requirement that v belong to a Kpt closure, that c be old-boring, that a seed end at top, that a selected tail be known, or that the old/new AlgorithmRuns exist. The assertion is strictly stronger than a zero column for the eligible `hStageOriginals` subset at that cut.

## E81.2 — actual stage zero without a Plan

Fix ANY root pool U⊆Fin N and ANY source selected-level set J⊆Nat (possibly J=R.I(c+1) for a genuine old run). Since E81.1 covers every eligible v:Fin N, it gives

    ∀ v∈hStageOriginals(normalizedGraphModel E,k,N,U,J),
      c+1≤A.freeLevel(v) => A.L.binary(c,v,0)=false.

No equality of the proposed retained Plan to the actual AlgorithmRun stage source, no positivity/zero at shadow-selected names only, no I2-free assumption, and no restrictions on U are used. A newly inserted bare-root original can belong to U without invalidating the lemma.

## E81.3 — whole-run consequence once E80 is verified

Use E80 with a subset Allowed of genuine old-range cuts such that, for each c<h in Allowed, there are idx,g with

    c = hPosition(k,idx,g)>0,  g<k, c<N,
    and E(idx,j)=false for all j.

By E81.1 each such cut satisfies E80's full-stage zero-column predicate automatically. Hence under exactly:

* one genuine old AlgorithmRun on X and one bare physical original `O_new` with coordinate in U;
* the E79 maximal COMPLETE OLD Kpt-prefix source witness per physical original among the eligible old-boring cuts in Allowed; and
* explicit true full physical no-novelty at all other old-boring cuts outside Allowed;

there exists a genuine target AlgorithmRun on Y=X∪{O_new} with EXACT RY.I=R.I and RY.F=R.F. No target Y-run is assumed.

This removes **all ordinary-L zero-stage geometric checks for the isolated-dummy base class**. The remaining prefix geometry is still substantive; an isolated dummy may have a new complete OLD E/L type with no old-live source witness at a given higher cut. Thus no claim that the dummy class is automatically quiet under arbitrary new roots.

## Boundaries

The lemma applies only to genuine lower real source generation g<k and c<N. It does NOT automatically handle the real TOP generation or arbitrary odd/fake auxiliary E cuts. It is tied to the true numerical-H+ ordinary-L generator and the literal original-Q isolated base condition; `role idx = dummy` requires the actual Q construction edge axiom to derive this isolation.

It is not a diary-uniform microevent count; N may grow. The K4 E/q2 cuts 10/22 remain visible whenever they occur as source levels, and are only covered if the exact eligibility and original-prefix witnesses hold. The COMMON labelled inverse-source monoid orbit, assigned successor characters, cross-occurrence normalization and sharp BRD remain open.

## Hostile checks (21)

1. E is the TRUE original-Q Boolean adjacency relation, not a chosen Kpt upper type map.
2. E81.1 requires only the original outward isolation `∀j E idx j=false`; graph symmetry is not necessary for the zero-bit conclusion.
3. The source cut is exactly c=hPosition(k,idx,g) with g<k.
4. The original coordinate c is physically within the N-carrier; don't drop c<N.
5. The tested v:Fin N is a genuine physical original coordinate, not a stage-generated Kpt parameter.
6. Only originals with c+1≤A.freeLevel(v) are claimed to have zero bit; shorter originals do not cross c.
7. The exact numerical-H+ ordinary-L generator is used; the auxiliary directed E relation is not symmetrized.
8. If L(c,v)=true then the verified original-Q base-neighbour theorem gives an actual j with E(idx,j)=true.
9. One base edge E(idx,j)=true contradicts dummy isolation, independent of j's selected status.
10. The zero-stage lemma is valid on ALL eligible physical v, so every candidate stage subset inherits it.
11. No old AlgorithmRun needed for E81.1 or E81.2.
12. No new Y-run is assumed at any point.
13. No stage-role Plan or selected-shadow coverage assumption is used in the zero-column lemma.
14. U may include the new bare-root original coordinate.
15. E80's Allowed may be disconnected; maximal E79 old-prefix certificates remain valid without interval assumptions.
16. E80 still needs genuine old-boringness and actual active-original source membership in the per-original eligibility filter.
17. Old-prefix witnesses are COMPLETE Kpt types including all directed E and negative L, not automatic from dummy isolation.
18. Other old-boring cuts outside Allowed remain explicit no-novelty obligations.
19. Positive even-real source cuts with NON-isolated original-Q base need separate reasoning; this theorem doesn't say their columns are zero.
20. K4 q2/E microcuts must be checked against genuine real/odd cut types; they are not globally discarded.
21. No uniform diary carrier, common labelled inverse-source orbit or sharp big Ramsey degree is claimed.

## Lean gate

Commit this English proof before the source code. Prove (a) the all-carrier eligible isolated-dummy zero original L bit; (b) the corresponding true stage-filter zero conclusion; (c) after E80 exact-head acceptance, the genuine whole-run I/F transport specialisation with only isolated original-Q class assumptions plus E79 maximal old-prefix tests and explicit outside-Allowed quietness. Register strict qualified standard-only axiom reports, dedicated direct Lake compile, negative parser self-test and independent full Lake build. Keep frozen black TeX and Sofia-deleted TODOs untouched; do not promote manuscript BLUE markers until accepted.
