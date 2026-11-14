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

## E25. Stronger result: **actual monoid I3 non-skippability** is a full-crossing invariant

The previous E24 proof transferred the *corrected (B3) verdict* between two physical no-(I1)/(I2) source closures. That is NOT enough to identify actual (I3) interestingness, because known arguments give non-skippable ⇒ failed corrected B3, not the converse in arbitrary finite stages.

There is, however, a **direct and stronger** approach: use the actual successor-tree monoid quantification, not the B3 age test.

Recall the genuine Kpt source definition `NonSkippableClosureCrossing family Z c`:

> There is no actual `Φ : ShapeMap (admissibleKptSTree family)`, with `Φ∈KptM family`, which skips exactly c and satisfies `Φ(ancestor z c)=ancestor z (c+1)` for EVERY node `z∈Z` crossing c.

The assertion that any *given* `Φ` satisfies these equations depends **only** on the canonical complete physical relation
`Cross_Z(c) = {(T,U) : ∃z∈Z crossing c, T=old(z,c), U=upper(z,c)}`.
No terminal Kpt node at c contributes a crossing equation.

### Monotonic transfer proof

Let `Cross_{Z₂}(c)⊆Cross_{Z₁}(c)`. Suppose a genuine Kpt shape map Φ respects all crossings of Z₁. Let z₂ be any crossing node of Z₂; take its exact old/upper full L+ pair (T,U). The relation inclusion yields some REAL crossing witness z₁∈Z₁ for the SAME pair. Since admissible Kpt nodes are *subtypes of complete raw partial types*, equality of their old raw types gives **literal equality** of the old Kpt ancestors, and similarly for the upper ancestors. Apply the Φ equation for z₁ and transport through these two equalities to obtain the equation for z₂. The actual monoid Φ and skip law have not changed.

Under equality of relations, repeat in both orientations. Thus

`NonSkippableClosureCrossing family Z₁ c ↔ NonSkippableClosureCrossing family Z₂ c`

for ANY two Kpt node sets, with **no no-I1/no-I2 premises** and no assumption of an `L`-age witness or B3 test. This is a genuine monoid-level result, not merely a type-profile sufficient condition.

### Recover complete local interestingness

The generic actual AlgorithmRun predicate `SMTree.Envelope.IsInterestingAt (normalizedKptSMTree family) Z c` is the disjunction:
1. a terminal node at c (I1);
2. a cut-level meet (I2);
3. no shape map in the **actual Kpt monoid** skipping the cut and respecting all closure crossings (I3).

The third condition is exactly the `NonSkippableClosureCrossing` predicate, because `normalizedKptSMTree family` has monoid `KptM family`.

If the two closures have the same terminal flag and the same complete physical crossing relation:
- If (I1) holds, they are both interesting by (I1).
- Otherwise their I2 status agrees by merged Track C's physical-fork theorem.
- If neither structural event occurs, their I3 non-skippability agrees by the new monoid result.
Hence their **full local IsInterestingAt truth values agree**, with no separate B3 premise and no need to match all individual pairwise meets.

One may refine this to identical PRIORITY FOUR-WAY event tags `I1/I2/I3/boring` at a common source-coordinate cut.

### Adversarial checklist

1. **Shape map is genuine.** Transfer the *same* actual Φ∈KptM; do not replace the monoid quantifier with an arbitrary map on selected shadows.
2. **Full old/upper types.** Kpt ancestor equality comes from identical complete dependent raw L+ types, including E; equality of ordinary L-reducts does not identify Kpt nodes.
3. **Two-sided relation equality.** One-way inclusion transfers a map respecting the larger relation to the smaller; equality is needed for equivalence of non-skippability.
4. **B3 is not I3.** A failed corrected B3 test need not by itself prove no skipping map exists. This argument works directly with the original monoid-level definition instead.
5. **I1 priority.** If a terminal source node exists at c, the raw I2 self-meet may also exist without any crossing fork; priority keeps the classification honest.
6. **No diary implication yet.** Equal unrefined macrodiaries have NOT been proved to yield identical full physical crossing relations and terminal flags; the K4 cuts 10/22 are live negative regressions.
7. **Source-coordinate cuts.** Different raw numerical H cuts may need a nontrivial normalization; this theorem assumes they are expressed at one common normalized Kpt source level c.
8. **Local interestingness is not full orbit.** Even equal local I1/I2/I3/boring tags at every cut do not by themselves construct a common fully labelled inverse-source monoid orbit, finite uniform carrier, or diary bijection. The full named parameter incidence and stage-by-stage normalization remain open.

**Lean targets:** monotonicity of genuine shape-map crossing constraints; equality of `NonSkippableClosureCrossing`; and direct equality of the actual `SMTree.Envelope.IsInterestingAt` predicate from terminal+crossing profile. Explicit isolated build, named standard-only transitive-axiom audit and full repository CI are mandatory before promoting any Lean validation marker.
