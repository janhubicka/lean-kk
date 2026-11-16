# Track D — generation-zero real old neighbour separates a selected top from a negative auxiliary source
16 November 2026 · English-first proof and adversarial audit **before Lean**.

## Scope and the unresolved manuscript step

The olive independent-set upper proof asserts that a selected future top type positive on an omitted event and a negative future auxiliary/cap type cannot first split at that event. Its proposed reason is an actual OLD original vertex v whose old-to-selected edge is positive but old-to-auxiliary edge is negative. The previous Track D candidate [#263](https://github.com/janhubicka/lean-kk/pull/263) formalizes the finite canonical singleton capacity ≤2 → old neighbour extraction; it has not yet proved this numerical H type-separation step. We isolate a new completely independent physical lemma about exact L+ old records.

The finite numerical-H constructor puts the real copy of old original v at generation 0:
`old0 = hPosition k v 0`.
For a physical tested cut at `c=hPosition k i g` with v<i and g≤k, the actual block order gives old0<c. For any **later** selected coding base j>i at TOP generation k, the exact H gate is always open and
`L_H(old0, hPosition k j k) = E(v,j)`.
For any later auxiliary base b>i at any bounded generation m≤k, if the original base graph has `E(v,b)=false`, numerical H preserves that nonedge:
`L_H(old0, hPosition k b m)=false`.

Therefore if `E(v,j)=true` and `E(v,b)=false`, a SAME old coordinate old0 strictly before the tested cut distinguishes the complete ordinary old-prefix L-types of selected top and negative auxiliary, and hence their full dependent old L+ types cannot be equal.

## Three exact claims

**(A) Generic old-type distinction.** Let A be any `EnumeratedPartialStructure 1 0 1`, cut, old<cut, and physical originals x,y (not assumed Kpt-eligible). If `A.L.binary old x 0=true` and `A.L.binary old y 0=false`, then `A.partialTypeAt cut x ≠ A.partialTypeAt cut y`. Proof: apply `lReduct` to hypothetical equality, use the checked `partialTypeAt_lReduct_eq_ofAgeModel`, and evaluate the two complete ordinary prefix types at `T.binary (some old) none 0`; this gives true=false. Auxiliary E and negative atoms are retained in the full source, not artificially assigned to an arbitrary L-only witness.

**(B) Physical zero-generation separation.** Fix any symmetric/irreflexive K4-free original E (the algebraic implication actually needs neither avoidance nor symmetry for this ONE directed bit), height k, and base order v<i<j, v<i<b. Let g,m≤k, and E(v,j)=true, E(v,b)=false. Then old0=hPosition k v 0 is below c=hPosition k i g, both target physical coordinates are above c, the actual H bit at old0 into selected top j_k is true, and the H bit into auxiliary b_m is false. The two target originals have distinct complete dependent old L+ partial source types at c.

**(C) Finite-carrier corollary.** When both future physical original addresses are actual `Fin N` elements and the tested cut c<N, the SAME distinction holds for the genuinely named finite numerical-H source. Do not claim source *closure membership* or E eligibility from L bits alone: only if separate actual Kpt source representation/eligibility is supplied can one apply this to exclude an I2 fork in a particular full closure.

## Proof sketch

- From v<i and 0≤k, verified `hPosition_lt_of_block_lt k v i 0 g ...` gives old0<c.
- From i<j and i<b and g≤k, the same formula places selected top and auxiliary physical addresses above c.
- The checked `numericH_older_generation_to_top_exact` gives the positive directed bit into j_k exactly `E(v,j)`. It includes the exceptional top-top tie, so the proof does not silently assume k>0.
- Checked `finiteNumericH_preserves_original_nonedge` gives the negative directed bit into b_m from E(v,b)=false, even when m=0 and regardless of generation gates.
- The complete-prefix type `RelationalPrefixType.ofAgeModel A.L cut original` actually records the L bit at `old0<cut`. Checked `partialTypeAt_lReduct_eq_ofAgeModel` translates it to the full dependent source `PartialTypeWithE`. The target old full L+ types differ already in ordinary L at old0.

## Hostile audit (17 checks)

1. Distinguish base graph adjacency E(v,j) from numerical H+ auxiliary E. We only prove an ordinary L statement.
2. The selected target is a real TOP-generation original at later base j>i; the negative target is a later base b>i at ANY m≤k. Same-base copies are excluded.
3. v is genuinely an *old Q base before the whole omitted event*, so v<i; without this premise v_0 might not precede the tested physical cut.
4. Positive top-column gate holds for generation zero even at k=0 by its exact top-tie disjunct, not a guessed 0<k assumption.
5. Negative base nonedge survives at ALL physical generations, including 0 and k; no symmetry assumption needed for this forward L bit.
6. To compare two full source types at level c, BOTH target physical names must be relevant Kpt original source names crossing c in the actual pre-cut closure. This is a separate application requirement and not inferred from this lemma.
7. The lemma distinguishes two physical upper original L+ prefixes; it does NOT prove that arbitrary meet/parameter nodes can have no I2 fork.
8. The source old-prefix L-reduct is evaluated at the actual physical old coordinate old0, not a selected diary shadow index.
9. The target selected and auxiliary names must actually belong to the final finite original-name carrier before claiming the result for an AlgorithmRun; the simple raw H Boolean table is total even outside the finite carrier.
10. The old Kpt full type contains E as well, but ordinary L inequality already forces full L+ inequality; do not invent E on a continuation witness.
11. The old base original v may be a reserved parameter and not a selected coding vertex; the proof only uses its actual Q adjacency bits.
12. A singleton graph-age bound ≤2 by itself is NOT sufficient to produce v unless age is the exact canonical finite old-column reference age, as the separate #263 audit stresses.
13. Negative-to-cap case is covered by E(v,b)=false for an isolated cap base b, but its actual Kpt free cut/seed membership is not supplied here.
14. A future auxiliary base b may have same old ordinary bit as selected elsewhere; the theorem compares the particular old v, not all future names.
15. The no-I2 proof requires pairwise checks on ALL active full Kpt nodes (including meet nodes), not merely selected-vs-negative pairs. This is one verified physical subcase only after Lean compilation.
16. No selected graph-age lower/upper BRD assertion follows from a finite physical bit.
17. Register exact qualified theorems with fresh strict standard-axiom gate; do not promote paper full-boringness mark.

## Proposed Lean

`Kk/K4GenerationZeroSourceSeparator.lean` imports `Kk.NumericHFullSelectedColumn`, `Kk.HBlockNonedges`, and mathlib. Prove:
- `finiteOldFullTypes_ne_of_distinguishing_L_bit`, generic complete-prefix bit separation.
- `finiteNumericH_old_zero_separates_top_from_negative`, with explicit old/base order and original E adjacency/nonedge, yielding physical chronology + positive/negative H bits + unequal full old dependent L+ source types.
Use no custom axioms or sorry; a dedicated exact-head direct module build and fully qualified `#print axioms` gate are required.

The next step is to combine this with the actual old-Q neighbour extracted by #263 and with exact pre-cut full Kpt source representation: then the selected positive and negative auxiliary physical originals cannot have equal old dependent L+ source types. Prove separately that all other pairs of full generated parameters/meets cannot fork at each omitted cut.

## Adversarial scope repair — explicit finite carrier (added before Lean corollary)

The bare numerical H Boolean table `hNumericBinary` is total on Nat even outside the `finiteNumericH(...,N).carrier`. Therefore the second theorem about two **numeric addresses** cannot, by itself, be used to claim either target is a named original in a particular finite AlgorithmRun. The English proposed finite-carrier corollary is a genuinely separate Lean statement, and must not be omitted.

New required endpoint `finiteNumericH_old_zero_separates_named_future_originals` adds:
- an actual physical cut `hPosition k cutBase g < N`;
- `selectedName auxName : Fin N` with their exact numerical address equalities to the selected top and negative auxiliary coordinates;
- a conclusion that the old generation-zero distinguishing coordinate is also strictly below `N`, AND the complete dependent old L+ partial types **of the two actual Fin N original names** are unequal.

The proof takes the already established oldZero<cut from the generic physical theorem, composes with cut<N for physical old carrier membership, and substitutes the two Fin N address equalities into the earlier full partial type inequality. It does **not** claim these two actual original nodes are in the Kpt pre-cut closure, nor that their free levels exceed the cut: that source-membership/eligibility bridge remains open.

This closes a real potential domain-of-definition ambiguity in the first draft without weakening the physically useful algebraic theorem. The new exact-head strict gate must register all THREE qualified endpoints, not only the initial two.
