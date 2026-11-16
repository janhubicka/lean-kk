# Track D — central integration of 14 independently verified finite cut theorems
16 November 2026. Source-first adversarial audit and exact-head gate plan.

## Base and previously verified sources

Branch starts from `janhubicka/lean-kk` main at `e6460faade1ae09c486a5db77bd89992be1823db`, with exactly **800** central `#print axioms` declarations. A successful previous full main run at `1753f46e` is [43762014560](https://github.com/janhubicka/lean-kk/actions/runs/43762014560); no success of a NEW 814-report gate is assumed before it runs.

The following six source modules are already merged to main and passed BOTH their exact-head dedicated strict named transitive-axiom tests and full Lean project tests. Do not replace the prior source proofs:

| Module | PR, dedicated gate | New central names |
|---|---|---|
| `Kk/B3OddFakeCut.lean` | [#223](https://github.com/janhubicka/lean-kk/pull/223), [43719705916](https://github.com/janhubicka/lean-kk/actions/runs/43719705916) | `henson_numericH_odd_cut_correctedB3` |
| `Kk/B3FailedCutGeneration.lean` | [#227](https://github.com/janhubicka/lean-kk/pull/227), [43730616001](https://github.com/janhubicka/lean-kk/actions/runs/43730616001) | `henson_failed_selectedB3_forces_lower_real_generation`, `henson_numericH_top_generation_cut_correctedB3`, `henson_failed_selectedB3_has_higher_generation_clique` |
| `Kk/ActualRunOddStructural.lean` | [#239](https://github.com/janhubicka/lean-kk/pull/239), [43731035231](https://github.com/janhubicka/lean-kk/actions/runs/43731035231) | `henson_numericH_odd_cut_unselected_of_no_I1_I2`, `henson_numericH_odd_selected_requires_structural_I1_or_I2` |
| `Kk/ActualRunOddFiniteIndex.lean` | [#244](https://github.com/janhubicka/lean-kk/pull/244), [43732030599](https://github.com/janhubicka/lean-kk/actions/runs/43732030599) | `henson_actualRun_odd_selected_has_indexed_I1_or_I2`, `henson_actualRun_odd_selected_has_constructed_indexed_I1_or_I2` |
| `Kk/ActualRunStructuralOrLowerReal.lean` | [#243](https://github.com/janhubicka/lean-kk/pull/243), [43731529990](https://github.com/janhubicka/lean-kk/actions/runs/43731529990) | `henson_actualRun_nonstructural_selected_has_lower_real_cut`, `henson_actualRun_selected_structural_or_lower_real_cut`, `henson_actualRun_selected_non_lower_real_requires_structural` |
| `Kk/PhysicalLowerRealCutNeighbour.lean` | [#245](https://github.com/janhubicka/lean-kk/pull/245), [43732575963](https://github.com/janhubicka/lean-kk/actions/runs/43732575963) | `physical_lower_real_cut_positive_generators`, `physical_lower_real_cut_positive_iff`, `finiteNumericH_eligible_lower_cut_neighbour_is_higher` |

Total **14 names**, 6 imports. The previous merged [PR #231](https://github.com/janhubicka/lean-kk/pull/231) already registered four distinct earlier finite nonempty-free cut-visible transfers; do not register those again.

## Proven finite math vs missing application

These fourteen results establish:
- physical odd cut corrected (B3) passes, but auxiliary E can still force real (I1)/(I2);
- full selected-stage failed B3 entails a real non-top cut, and a genuine K_ell witness whose upper original names have strictly higher numerical generation;
- true selected AlgorithmRun cuts are explained by full-source (I1), (I2), or a real non-top generation;
- selected odd cuts have exact finite full-Kpt active node certificates for structural (I1)/(I2) using full negative ordinary-L and auxiliary E records;
- strictly later positive physical cut neighbours of a real non-top cut have later original BASE and higher generation, and exact physical base L bit.

None of these identifies the selected diary front with the complete Kpt parameter closure or demonstrates that the chosen upper-L type of every auxiliary full positive cut neighbour is represented in the marked source. The direct small-independent full-boringness lemma and common labelled inverse source are still **pending**. Do not upgrade those or global BRDs.

## File-change discipline and acceptance

Edit ONLY `Kk.lean` to add six imports, and `scripts/check_axioms.lean` to append fourteen exact `#check @Kk...` / `#print axioms Kk...` reports; preserve the earlier 800 names, order and existing source imports. Add this audit note. No proof statements or source module bodies are changed.

The target total must be **814 distinct, exactly qualified** `#print axioms` lines, with no duplicate symbol. The new `Lean` workflow must run a complete `lake build`, full named reports, `check_axiom_report.py --self-test`, and the strict transitive-axiom gate at THIS exact integration head. A previous successful dedicated gate, merge, or main checkout does NOT substitute for new full-build evidence. If failure, repair English/registration first.

The manuscripts have existing historical pins. A future separate review may add scoped BLUE finite validation marks after this central gate completes; never silently repoint older frozen proof markers without comparing all registered names and updating the exact marker registry. Concurrent manuscript Track A/B/C/F changes are not rewritten by this integration.
