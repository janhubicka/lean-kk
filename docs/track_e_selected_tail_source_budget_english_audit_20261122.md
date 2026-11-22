# Track E E87 — a suffix-selected-level budget for maximal physical OLD-Kpt-prefix obligations

**22 November 2026. English proof and adversarial audit committed BEFORE Lean code.**

## Why E86 can be sharpened

E86, exact-head verified and merged in PR #451, bounds the number of distinct physical numerical-H+ originals that need a maximal OLD Kpt-prefix witness test by

    Need.card ≤ U.card + |R.I(0)|,

with the selected-level cardinal represented by an actual Finset. Unlike the older E85 bound by oldTop+1, this is already independent of arbitrarily long physical gaps between selected levels.

A frequent application, however, checks only source cuts **not below an already processed stage** c₀. The selected ORIGINAL stage at such cuts is controlled by the suffix of the old selected-level set, not by the whole selected set. We can remove all earlier selected levels from the budget, again without replacing the genuine source by a selected-age shadow.

## Exact setup

Take an arbitrary normalized forbidden Kpt family, a genuine finite numerical-H+ original structure A=finiteNumericH(K,k,N), its finite true root-original pool U⊆Fin N, one **genuine old** normalized Kpt AlgorithmRun R on seeds X to scan top h, any candidate new seeds Y (no AlgorithmRun assumed), and any Allowed set of literal source cuts.

Fix a cutoff c₀ with c₀<h. Require

    ∀c∈Allowed, c₀≤c.

We do not require Allowed to be an interval, or all its cuts to be boring/zero-column: E79's actual eligible cut membership imposes genuine old-boringness and a genuinely new-live crossing separately.

The finite set `Need` is E85's actual physical original-name support: v∈Need iff its E79 Allowed eligible-cut set is nonempty. This counts only physical originals representing actual new-live full Kpt crossing sources at old-boring cuts.

Define the **selected old suffix Finset**

    SelTail(c₀) =
      (Finset.range(h+1)).filter(fun q => q∈R.I(c₀+1)).

The checked genuine old-run selected-level bounds `R.I_mem_bounds` show that for c₀<h this is an exact finite representation of R.I(c₀+1). The top h is included; an exclusive range(h) would be incorrect.

## Lemma E87.1 — needed originals lie in one later true original stage

If v∈Need, choose a real eligible old-boring cut c∈S_v. It lies in Allowed, so c₀≤c; and c<h by E79. The genuine E79 membership theorem gives

    v ∈ hStageOriginals(K,k,N,U,R.I(c+1)).

Use the verified actual run tail identity

    R.I(c+1) = {q∈R.I0 : c+1≤q}
    R.I(c₀+1) = {q∈R.I0 : c₀+1≤q}

(with both tails defined at indices ≤h). Because c₀≤c, the first set is included in the second. The verified original-stage monotonicity from E85 then yields

    v ∈ hStageOriginals(K,k,N,U,R.I(c₀+1)).

Thus

    Need ⊆ V(c₀)=hStageOriginals(K,k,N,U,R.I(c₀+1)).

This is a source-exact suffix property, not a claim that v itself belongs to either OLD or NEW Kpt closure.

## Lemma E87.2 — selected suffix controls its physical original stage

Let

    T(c₀) = {v:Fin N : v.val∈R.I(c₀+1)}.

The exact finite stage-original definition says every v∈V(c₀) belongs either to U or to T(c₀) with positive genuine free E-level. Hence V(c₀)⊆U∪T(c₀).

Map each v∈T(c₀) by its literal numerical coordinate v.val into SelTail(c₀). This is well-defined by selected-tail membership and `R.I_mem_bounds`, and injective because distinct Fin N physical addresses have distinct numeric values. Thus

    T(c₀).card ≤ SelTail(c₀).card

and consequently

    V(c₀).card ≤ U.card + SelTail(c₀).card.

No disjointness assumption between U and selected physical originals is needed.

## Theorem E87 — suffix budget

Under c₀<h and the Allowed cutoff assumption,

    Need.card ≤ U.card + SelTail(c₀).card.

Furthermore SelTail(c₀) is a subset of the genuine selected-old Finset SelOld=SelTail(-1) constructed in E86, so

    SelTail(c₀).card ≤ SelOld.card,

and E87 is at least as strong as the earlier E86 numerical bound.

This is a **strict improvement whenever the old run has selected levels below c₀+1**. It can be used in a descending source construction to charge each later suffix against genuinely remaining selected parameters; the number of possible original OLD-prefix tests cannot increase simply by padding the physical carrier or inserting early selected blocks that no longer appear in the current stage.

## What is NOT proved

- There is no bound by the ABSTRACT DIARY until the sizes of the genuine root-original pool U and its selected-tail cardinal are controlled through the resolved diary construction.
- The theorem counts distinct maximal complete OLD Kpt-prefix *test obligations*, not failures, their interval lengths, or actual witnesses. G474's factor-Bad charge is consistent with this distinction and does not convert a carrier bound into an event-count bound.
- The maximal old-prefix source witnesses are NOT constructed for the resolved-Q/Henson diary.
- No source-coordinate normalization across different diary occurrences, common labelled inverse-source monoid orbit or sharp BRD upper/lower equality is established.
- Genuine K4 auxiliary q2/E cuts, notably the physical 10/22 tests where relevant, are not removed.
- We do not assert that every old-boring cut is isolated-dummy, zero-real, or safe-odd. Other-cut physical quietness remains the explicit E84 hypothesis.

## Hostile adversarial checks (22)

1. `R` must be a genuine OLD AlgorithmRun, not an arbitrary family of level masks.
2. The new source Y is arbitrary; no new run on Y appears among the hypotheses.
3. The cutoff c₀ is < h, so c₀+1≤h and `R.I(c₀+1)` has a verified tail equation.
4. Every Allowed cut is ≥c₀; just requiring the maximal cut of the UNION to be ≥c₀ would be insufficient.
5. E79's eligibility includes actual old-boringness and genuine new-live crossing source membership, not merely v∈Fin N.
6. Need is a Finset of PHYSICAL original coordinates, not source Kpt nodes or graph-age types.
7. `c∈S_v` gives both c<h and v∈true stage original pool at `R.I(c+1)`.
8. For c<h, c+1≤h; never call the run tail identity beyond top.
9. `c₀≤c` implies c₀+1≤c+1; selected tails include later levels, so `R.I(c+1)⊆R.I(c₀+1)` (the direction matters).
10. E85's stage original pool is monotone with respect to selected level SET inclusion.
11. U is fixed across this comparison; no hidden new original-pool expansion.
12. Original v need not itself be an OLD-LIVE source Kpt node.
13. The selected-tail Finset uses inclusive range(h+1), retaining topI.
14. `R.I_mem_bounds (c₀+1)` certifies q≤h for all tail members.
15. An original selected from the tail is counted by its literal coordinate v.val, not an abstract isomorphic type.
16. The injection from Fin N addresses to Nat selected levels is exact, even when N is much larger than h.
17. `V(c₀)⊆U∪T(c₀)` follows by forgetting only positive E-free-level eligibility, so it is a sound upper approximation.
18. U and T(c₀) may overlap; the union cardinal inequality is used, not an unjustified disjoint sum.
19. Allowed may be disconnected and may include multiple safe classes; the proof needs no convexity.
20. The budget is for distinct maximal original-name tests and does not count actual bad cuts or witness failures.
21. No diary-uniform selected-tail bound, source-label transport, inverse orbit or BRD count is smuggled in.
22. K4 E/q2 and unsafe odd E-free-end physical cuts remain genuine possible obstructions.

## Lean acceptance

Write a standalone E87 module importing E86 and E85, with (a) exact finite selected-tail membership, (b) Need⊆the true original stage pool at c₀+1, (c) the stage-pool cardinal bound, and (d) the final Need cardinal theorem plus selected-tail⊆all-selected. Use only existing verified AlgorithmRun `R.I_eq_final_tail_of_run`, `R.I_mem_bounds`, stage original monotonicity, Finset injection and cardinal theorems. English proof precedes Lean. Require exact-head standalone Lake compilation, named strict standard-only transitive-axiom reports including negative parser self-test, and independent whole project build before merging or annotating the manuscript. Do not alter frozen black text or re-add Sofia-deleted TODOs.
