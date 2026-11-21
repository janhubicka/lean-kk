# Track E E86 — bound maximal OLD Kpt-prefix obligations by |U| + number of selected OLD levels, not by scan height

**21 November 2026. English-first mathematical proof and 24 adversarial checks, committed before Lean.**

## Sharper source-count conclusion

E85 (draft Lean PR #444 under independent CI) establishes that the number of physical numerical-H+ original coordinates v requiring an E79 maximal complete OLD Kpt-prefix test is at most

    |U| + (oldTop+1).

This is already independent of the new physical numerical-H+ carrier N, but oldTop is a PHYSICAL coordinate and may be arbitrarily inflated by gaps in the realized enumeration. It is therefore not yet an optimal source budget.

The actual final OLD original-stage pool has a much sharper exact description

    V = hStageOriginals(K,k,N,U,R.I(0))
      = U ∪ {v:Fin N | v.val ∈ R.I(0) and A.freeLevel(v)>0}.

The only physical originals outside U are literally indexed by DISTINCT old selected levels. Hence

    |Needed maximal original-prefix tests|
       ≤ |V|
       ≤ |U| + |R.I(0)|.

The set R.I(0) of genuine selected source levels is FINITE for one true AlgorithmRun with top h, and its membership lies in the inclusive interval [0,h] by the verified `R.I_mem_bounds`. No new run, no source-type quotienting, no unverified diary Plan, and no uniform physical carrier assumption are required.

**Key point:** the right-hand side counts the NUMBER OF ACTUALLY SELECTED LEVELS, not the numerical span to the top. It is therefore invariant under inserting arbitrarily many boring physical gaps into the old scan. This is a significantly better bridge toward a bound depending on the finite diary envelope.

## Exact finite selection set

For a true old AlgorithmRun R of top h, define its selected-level FINSET

    Sel(R) = (Finset.range (h+1)).filter (fun q => q∈R.I(0)).

This is a finite subset of [0,h], and the checked `R.I_mem_bounds` proves

    q∈Sel(R)  iff  q∈R.I(0).

The +1 is necessary because `R.topI` includes h. The source scan's literal selected-level set may include its top, and assuming strict q<h is wrong.

## E86.1 — each nonroot final stage original injects into Sel(R)

Let

    T=(Finset.univ:Finset(Fin N)).filter(fun v => v.val∈R.I(0)).

This contains every selected physical original, dropping the positive E-free cut condition for an upper bound.

The map f:T→Sel(R) given by f(v)=v.val is well-defined because v∈T implies v.val∈R.I0 and hence v.val≤h. It is injective because different `Fin N` addresses have distinct natural values. Therefore by the standard finite-injection cardinal theorem,

    |T| ≤ |Sel(R)|.

This is strictly stronger than merely |T|≤h+1 when R.I0 is sparse.

## E86.2 — final OLD original-stage pool has small cardinal

Unfold `hStageOriginals`. Every v∈V is either in U or selected in R.I0 with positive canonical E-free level. Hence V⊆U∪T and

    |V| ≤ |U∪T| ≤ |U|+|T| ≤ |U|+|Sel(R)|.

The root pool U need not be disjoint from the selected original set; using the union inequality is sound without extra assumptions.

## E86.3 — required maximal old-source tests inherit the bound

By E85's verified physical-stage argument (once its exact-head CI passes), the E79 original-name set Need of all v with NONEMPTY eligible old-boring Allowed physical crossing support satisfies Need⊆V. Hence

    |Need| ≤ |U|+|Sel(R)|.

At each v∈Need, E79 requires at most one maximal old-Kpt-prefix matching test over the chosen Allowed cut class union. Consequently the NUMBER of different maximal old-prefix tests is bounded by the old root original pool size plus the number of ACTUALLY SELECTED OLD source levels, independent of N and independent of large boring stretches.

This does not say the maximal matching witnesses actually exist or that any upper source type is matched without a full zero-column hypothesis. At other cuts, E80/E84 still require explicit physical quietness.

## Implications and remaining gaps

A genuinely diary-uniform budget would follow if the old source selected-level count |Sel(R)| and old physical original-root pool |U| are uniformly bounded in terms of the FIXED diary (or its verified envelope), independent of embedding into the larger Henson graph. This is plausible but NOT established by E86. One must still prove that resolved-Q original-prefix witnesses at the maximal cuts exist and control remaining nonzero/unsafe odd/auxiliary cut classes, including actual K4 q2/E events.

The separate common labelled inverse-source monoid orbit, assigned successor characters, and arbitrary-occurrence source-coordinate normalization remain open.

## Hostile audit (24)

1. R is one TRUE Kpt AlgorithmRun, not an arbitrary Boolean selected-level mask.
2. Its I(0) is a SET, not a Finset; Sel(R) is the exact finite representation.
3. `R.I_mem_bounds` gives q≤h, not q<h.
4. The chosen Finset.range(h+1) includes h, preserving topI.
5. The selected-level set may be sparse; |Sel(R)| can be MUCH smaller than h+1.
6. Every source original v∈V outside U has literal v.val∈R.I0, not merely a matching graph-type code.
7. The exact original-stage definition also requires positive freeLevel; dropping it yields an upper bound T.
8. The map v↦v.val from Fin N into Nat is injective.
9. R.I0 membership ensures f(v) lies in Sel(R), so no illegal map to an unrelated cut.
10. V⊆U∪T is a physical finite-stage containment, not source closure equality.
11. U can overlap selected originals; the union CARDINAL upper bound is used.
12. Actual eligible E79 original names Need⊆V comes from stage selected-tail monotonicity, not guessed source-orbit properties.
13. Need can be empty, including when all new source events are already old-live.
14. Need may have multiple original representatives for one Kpt source node; count is per physical original, still bounded by V.
15. One original may represent many new auxiliary parameters/meets; only one maximal OLD-prefix test is charged by E79.
16. Allowed may interleave isolated dummy and odd safe cuts or omit arbitrarily many other cuts.
17. The bound controls the NUMBER of maximal test obligations, not the length or number of bad source cuts on failure.
18. The old physical carrier N is arbitrary finite; none of the right-hand side counts N.
19. Arbitrarily many boring numeric gaps may increase h without increasing |Sel(R)|; E86 improves E85 in that situation.
20. The selected count |Sel(R)| itself may vary with the chosen diary occurrence; no uniform diary bound is silently inserted.
21. The physical root pool size |U| must be controlled separately by the diary realization.
22. The actual old-prefix witness equality is complete Kpt ancestor equality, including E and negative L, not a positive-L shadow.
23. Unsafe odd E-free-end and K4 q2/E microcuts remain; no zero-column/terminal classification is claimed.
24. No common labelled inverse-source monoid orbit, all-occurrence normalization or sharp BRD upper/lower theorem follows.

## Formal validation gate

After E85 has its own green exact-head Lean source and merges, create a standalone E86 module importing E85's true Need⊆V theorem and Mathlib finite-cardinality API. Formalize `Sel(R)`, exact membership equivalence, `|V|≤|U|+|Sel(R)|`, and the inherited `|Need|≤|U|+|Sel(R)|`. Use `Finset.card_le_card_of_injOn` to inject selected physical original coordinates into Sel(R), with the inclusive `R.I_mem_bounds` proof. Commit English before Lean, require strict named standard-only axiom reports with negative parser self-test, direct Lake compilation and independent full project build. Keep protected black TeX unchanged and global diary-uniform validation markers pending.

## Stacked source acceptance note

This E86 Lean branch is intentionally based on the corrected E85 source branch `kk-track-e-old-top-max-original-budget-20261121` to reuse `Need⊆V`. E85's exact-head CI acceptance and merge are separate gates: E86 may compile here, but must not be merged ahead of E85. Its selected-level cardinal bound is mathematical and source-relative, NOT a uniform diary carrier estimate.
