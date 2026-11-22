# Central Lean declaration audit closure (22 November 2026)

## Scope and finding

The central `scripts/check_axioms.lean` currently contains 1,065 qualified
`#check` declarations but only 1,017 distinct `#print axioms` commands.
There are **48 checks with no corresponding transitive-axiom report**. These
checks are genuine, and some may already be covered transitively by other
registered results, but that must not be assumed for an adversarial review.

Of the 48, **four are imported successor-tree API theorems**;
the remaining 44 are `Kk` declarations, including representing-pair,
labelled source actions, the exact K4 auxiliary gadget, and the Henson
one-point graph edges. Each needs a qualified direct axiom report at
the exact current pinned dependency.

## Complete list of previously unreported declarations

1. `SuccessorTree.V10.normalizedKpt_typeRespectingRamsey`
2. `SuccessorTree.V10.TypeRespectingEmbedding.exists_extension`
3. `SuccessorTree.V10.TypeRespectingEmbedding.act_apply`
4. `SuccessorTree.V10.TypeRespectingEmbedding.act_comp`
5. `Kk.FiniteRepresentingPair.imageVertex_eq_of_vertex_eq`
6. `Kk.FiniteRepresentingPair.imageVertex_act`
7. `Kk.FiniteRepresentingPair.imageVertex_e`
8. `Kk.LabelledGPlusCopy.fromPairs_binary`
9. `Kk.LabelledGPlusCopy.fromPairs_e`
10. `Kk.FiniteRepresentingPair.fromCommonUpperFamily_injective`
11. `Kk.LabelledGOmegaCopy.toGPlus_map`
12. `Kk.LabelledGOmegaCopy.map_lt_of_prefix`
13. `Kk.forwardAsymPattern_irreducible`
14. `Kk.backwardAsymPattern_irreducible`
15. `Kk.cliquePattern_irreducible`
16. `Kk.strictMono_fin_nat_eq_of_same_range`
17. `Kk.labelled_codes_eq_of_same_range`
18. `Kk.fullBefore_valid`
19. `Kk.fullAfter_valid`
20. `Kk.labelled_prefix_chains_eq_of_common_top_and_sizes`
21. `Kk.hensonForbiddenFamily_patternCard_le`
22. `Kk.B3_no_new_asym_pair`
23. `Kk.afterK4_lt_beforeK4`
24. `Kk.uniformAfter_lt_before`
25. `Kk.fourCliqueCore_finite`
26. `Kk.fourCliqueCore_sameSocle`
27. `Kk.fourCliqueCore_upper_types`
28. `Kk.fourCliqueCore_realizesK4`
29. `Kk.k4Cut22_finite`
30. `Kk.k4Cut22_sameSocle`
31. `Kk.k4Cut22_upper_types`
32. `Kk.k4Cut22_realizesK4`
33. `Kk.k4FourOriginalEdge_symmetric`
34. `Kk.k4FourOriginalEdge_irreflexive`
35. `Kk.k4H_old_binary_true_iff`
36. `Kk.k4H_upper_edge_true_iff`
37. `Kk.k4H_all_diagonals_false`
38. `Kk.k4H_top_binary_loop_false`
39. `Kk.k4H_cut22_prescribed_socle`
40. `Kk.k4Cut10_finite`
41. `Kk.k4Cut10_sameSocle`
42. `Kk.k4Cut10_upper_types`
43. `Kk.k4Cut10_realizesK4`
44. `Kk.k4H_cut10_old_binary_false`
45. `Kk.k4H_cut10_prescribed_socle`
46. `Kk.onePointGraphEdge_old`
47. `Kk.onePointGraphEdge_right`
48. `Kk.onePointGraphEdge_left`

## Validation rule and expected result

Append exactly one `#print axioms` for each of these 48 *already
typechecked* names, without changing any theorem statement, root import,
mathematical proof, dependency pin, or previous registration. The complete
main gate must build and parse exactly **1,065** unique reports, each with
axioms a subset of `{propext, Classical.choice, Quot.sound}` and no
`sorryAx` or `unknownConstant`.

If a previously unchecked dependency fails this gate, do NOT remove it
or weaken the script; report the precise dependency and repair its proof
or manuscript citation first. If all pass, this removes a real
verification-coverage asymmetry but does **not** prove the unformalized
Kk-free diary occurrence or the global BRD characterization.

This is the second adversarial audit track alongside the independent
finite physical cover-history strengthening. No frozen black TeX is
modified.
