# Track E: priority-aware structural microevent comparison from minimal full Kpt cut profile

**14 November 2026. English proof and hostile audit prepared before Lean.**
Parent: [KK Track E #27](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/issues/27). New branch from `lean-kk` main `b93d5fe1c5cd421a9202b3b0607683308587e426`.

## E21. What the merged physical source theorems now show

Merged Track E #127 supplies the complete actual Kpt crossing relation at **every** cut of a true finite numerical H+ AlgorithmRun from ONE exhaustive finite source node index, and actual active-node witnesses of structural (I1) and (I2). Merged Track C #131/#133 strengthens the reverse (I2) classification:

- A *fork* of the complete dependent old/upper L+ crossing relation (one full old type with two distinct full next types) always forces a meet at the tested cut, even without an (I1) restriction.
- Conversely, a meet at that cut with **no actual terminal source node at that same cut** forces a fork.
- Thus **when (I1) is false**, (I2) is equivalent to full crossing-relation nonfunctionality.

One cannot erase the no-(I1) qualification! The literal (I2) meet predicate allows a degenerate self-meet `meet(x,x)=x`. In particular if a source node x of level c belongs to Z, both raw predicates (I1) and (I2) may hold at c, while no distinct next-upper crossing is forced. Algorithm 5.4 checks (I1) first. The correct invariant is therefore **priority structural status**, not a pair of unconditional raw I1/I2 truth values.

## E22. Two physical Kpt closures, the same **minimal local** source profile

Fix the same normalized admissible Kpt language/family, a common source-coordinate cut c, and TWO possibly different genuine physical Kpt node sets Z₁,Z₂. Assume ONLY:

1. **Terminal flag agreement:** `KptI1AtCut family Z₁ c ↔ KptI1AtCut family Z₂ c` (equivalently: both have or both lack a node terminating at the cut).
2. **Complete crossing spectra agreement:**
   `FullPhysicalClosureCrossing family Z₁ c = FullPhysicalClosureCrossing family Z₂ c`, including all full old+upper L+ pairs and auxiliary E.

Then their priority statuses agree EXACTLY:
- (I1) vs (I1) from the terminal flag.
- If not (I1), (I2) vs (I2) from the complete fork/nonfunctionality equivalence and crossing equality.
- If neither, both remain in the *nonstructural* case for further (B3)/(I3) analysis.

**Proof.** Case-split on the common terminal flag. If true, both statuses are (I1), and no assertion about raw (I2) is necessary. Otherwise apply the verified Track C `kpt_no_I1_I2_iff_physical_crossing_nonfunctional` in each closure. Equality of full crossing sets identifies the existential old+two-distinct-upper witness formula on both sides, hence the raw I2 flags and their negations. This gives the three cases and excludes any hidden requirement to compare every pairwise meet at that one cut.

**Improvement over the earlier Track E contract.** We need *not* identify the underlying Kpt node sets, individual source-name IDs, or all pairwise meets merely to decide the PRIORITIZED (I1)/(I2) event kind. We still do need those data to reconstruct a complete labelled envelope/orbit: comparing priority tags is strictly weaker than identifying full named parameter incidence and inverse images.

## E23. Finite indexed version and (B3) consequence

Track C's exact finite run indices `nodeᵢ : Pᵢ → Kpt`, `liveᵢ(c,j)`, may have DIFFERENT finite cardinalities. Their exact coverage equations imply:

`I1(Zᵢ,c) ↔ ∃j∈Pᵢ, liveᵢ(c,j)=true ∧ lev(nodeᵢ j)=c`.

The new indexed comparison therefore needs only (a) **equivalence of these terminal-witness flags** and (b) **equality of the complete indexed crossing relations**. The latter follows from previously verified Track E's *two-sided full old+upper pair-matching criterion*, without any bijection of entire indices. Apply E22 to infer identical priority structural event classification across the two physical closures.

If both are in the nonstructural case, the above proof supplies no-(I1) and no-(I2) in BOTH closures. For two genuine finite numerical H+ presentations with complete original-name pool representation, this allows Track E #107's physical `two_numericH_closures_B3_of_equal_full_crossing_relation` to conclude equality of the complete corrected (B3) truth value (not just the selected-shadow verdict) from the same crossing relation equality. One needs no independent no-(I2) premise on the SECOND occurrence once the first is structurally noninteresting and the two terminal/crossing profiles agree.

### Adversarial checklist

1. **I1 priority is essential:** a terminal node x at the cut witnesses a trivial I2 self-meet but no fork necessarily. Never assert raw I2 iff fork unconditionally.
2. **Completeness of source records:** the crossing relation is that of ALL closure Kpt nodes, not selected original branches; K4 auxiliary cuts 10 and 22 remain real.
3. **Need terminal witness:** complete crossing spectra at ALL cuts can miss terminal prefixes (merged E17–E20 negative regression). Terminal membership cannot be inferred from the pair spectrum.
4. **Need full L+ pairs:** equality of ordinary-L reducts alone does not imply equality of Kpt successor E records. Corrected B3 itself is L-only; the physical comparison is stronger.
5. **Different index sizes:** two-sided crossing-pair matching is weaker than a bijection of full nodes; that is adequate for priority event and full B3 only, NOT for the labelled orbit.
6. **Source-normalized cuts:** raw numerical positions can differ by inserted boring levels; the theorem fixes a common Kpt cut coordinate. Constructing a common cut normalization from the diary remains OPEN.
7. **Actual run relevance:** the finite index at each occurrence must exhaust the TRUE closure `closure (... R.I(c+1)) X`; a filtered marked selection cannot substitute for it.
8. **No I3 equivalence:** even equality of structural status and B3 verdict does not on its own prove matching selected levels or true I3/non-skippability; actual AlgorithmRun selection/successor maps must be compared.
9. **No uniform bound yet:** finite `|Pᵢ|` for each ambient N is not a diary-size-uniform bound.
10. **Labels and source orbit:** full selected-vertex inverse image chains, dependent parameter transport, and a common outgoing monoid source remain separate requirements.

## Proposed Lean endpoints

- Priority classification theorem across two arbitrary physical Kpt closures from terminal-flag and complete crossing equality.
- Explicit negative regression: any genuine terminal node at the cut witnesses raw I1 **and** degenerate raw I2.
- Indexed finite comparison theorem from exact source-index coverage, equivalent terminal flags and equal indexed full crossings (with no assumed name bijection).
- Concrete numerical H+ transfer of no-(I2) and corrected (B3) under the above source profile, possibly separately gated if the Lean type parameters become too unwieldy.

All statements are **conditional** on the actual local profile agreements. No assertion that same unrefined KK macrodiary supplies them. No global envelope/carrier or upper BRD validation marks should be promoted on this basis.
## E24. Physical two-numerical-H B3 transfer with only ONE no-(I2) input

The prior merged cross-numerical-H theorem `two_numericH_closures_B3_of_equal_full_crossing_relation` requires no-(I2) in **both** physical source closures. Under the new minimal local profile comparison, the SECOND no-(I2) premise is no longer independent.

Take two genuine finite numerical H+ presentations `A₁=finiteNumericH K₁ k₁ N₁` and `A₂=finiteNumericH K₂ k₂ N₂`, the same normalized forbidden family and a common source-coordinate cut c, with complete Kpt closure sources `Z₁,Z₂`. Suppose each finite original-name pool actually represents every node of its respective closure (the explicit Track C `hPool` hypothesis). Suppose (I1) is **absent** and no competing (I2) meet occurs in `Z₁`, and suppose the terminal flag agrees and their **FULL physical** old+upper L+ crossing relations agree.

Then:
1. (I1) and (I2) are both absent in `Z₂`, by E22 priority transfer and the verified no-I1 fork equivalence.
2. Both canonical `closureSelectedBoringData` prescribed source maps therefore satisfy the physical no-I2 crossing coverage/graph theorem.
3. Their source domains and full assigned upper L+ outputs coincide, and their corrected (B3) truth values coincide, by merged Track E `two_numericH_closures_B3_of_equal_full_crossing_relation`.

This is a **real physical reduction** of the cross-occurrence comparison assumptions, not a proof that diary equality supplies the terminal and crossing agreement. The second no-(I2) test has been *derived* instead of postulated. No I3 selection or boring-level classification is inferred solely from the B3 verdict.

**Hostile test.** A one-sided no-(I2) premise without common terminal flags is insufficient: a new terminal prefix in the other closure may create a degenerate raw (I2) self-meet while leaving every crossing relation unchanged. Thus the terminal-flag hypothesis must not be dropped. If (I1) holds in the first closure, it gets priority but the first/second raw (I2) values need not match; the B3-stage theorem is only applied on the common genuinely nonstructural branch.
