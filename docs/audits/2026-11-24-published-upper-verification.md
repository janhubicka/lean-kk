# Published upper-validation evidence

24 November 2026. The immutable proof source is
[`3e1bfc9384213daea88f92bf9faad4941a40544e`](https://github.com/janhubicka/lean-kk/commit/3e1bfc9384213daea88f92bf9faad4941a40544e),
with tree `73c51a86c38afde0bdd3143fdc38d3aedc117a29`.
This report records hosted verification of that source; subsequent documentation
commits do not change the audited proof files.

## Directly inspected gate logs

- Root run [45405415472](https://github.com/janhubicka/lean-kk/actions/runs/45405415472),
  job 138484692981: `Build completed successfully (9951 jobs)` and
  `PASS: 1195 exact transitive-axiom reports; only Classical.choice, Quot.sound, propext`.
- Focused run [45405415419](https://github.com/janhubicka/lean-kk/actions/runs/45405415419),
  job 138484692131: its declared module build completed (9621 jobs), then
  `PASS: 88 exact transitive-axiom reports; only Classical.choice, Quot.sound, propext`.
- Both logs also report successful rejection self-tests for missing, extra,
  and custom-axiom reports. The focused inventory is the prior 25 plus all
  63 new public endpoints; the central inventory is the prior 1132 plus 63.

The corresponding local full build and both strict audits independently
passed. Their source and log hashes are recorded in
`2026-11-24-proof-source-manifest.json`.

## Complete reported workflow inventory

All twenty pull-request workflow runs returned by the commit endpoint were
observed completed successfully before this report was committed.

| Workflow | Run | Result |
| --- | --- | --- |
| KK Track D — concrete Henson top seeds dummy and selected lower cut skip | [45405415270](https://github.com/janhubicka/lean-kk/actions/runs/45405415270) | success |
| KK Track D — actual empty physical cut-star B3 elimination | [45405415452](https://github.com/janhubicka/lean-kk/actions/runs/45405415452) | success |
| KK Track D — descending stage role to true marked B3 | [45405415387](https://github.com/janhubicka/lean-kk/actions/runs/45405415387) | success |
| KK Track B automatic age-cover kernel gate | [45405415496](https://github.com/janhubicka/lean-kk/actions/runs/45405415496) | success |
| KK Track A candidate descendant complete raw old-socle seed | [45405415218](https://github.com/janhubicka/lean-kk/actions/runs/45405415218) | success |
| KK Track A/G odd full-Kpt factor Bad socle trichotomy | [45405415346](https://github.com/janhubicka/lean-kk/actions/runs/45405415346) | success |
| KK Track B canonical-slack kernel gate | [45405415205](https://github.com/janhubicka/lean-kk/actions/runs/45405415205) | success |
| KK Track D — genuine zero-stage no-I1/no-I2/no-I3, dummy and selected lower | [45405415497](https://github.com/janhubicka/lean-kk/actions/runs/45405415497) | success |
| KK Track A residual dependent Kpt profile defect budget | [45405415412](https://github.com/janhubicka/lean-kk/actions/runs/45405415412) | success |
| KK Track A/G odd indexed structural and missing-old-socle budget | [45405415209](https://github.com/janhubicka/lean-kk/actions/runs/45405415209) | success |
| KK upper continuation — full-age B3 and retained plans | [45405415419](https://github.com/janhubicka/lean-kk/actions/runs/45405415419) | success |
| KK Track A odd old-lower-socle maximal frontier | [45405415206](https://github.com/janhubicka/lean-kk/actions/runs/45405415206) | success |
| KK Track A exact real numeric cut raw event | [45405415378](https://github.com/janhubicka/lean-kk/actions/runs/45405415378) | success |
| KK Track A exact physical ordinary-L raw cut spectrum | [45405415571](https://github.com/janhubicka/lean-kk/actions/runs/45405415571) | success |
| KK whole-repository Lean source coverage audit | [45405415414](https://github.com/janhubicka/lean-kk/actions/runs/45405415414) | success |
| KK Track A/G exceptional full-Kpt selected-level localization | [45405415194](https://github.com/janhubicka/lean-kk/actions/runs/45405415194) | success |
| KK Track A exact-head sharp Henson age verification | [45405415495](https://github.com/janhubicka/lean-kk/actions/runs/45405415495) | success |
| Lean | [45405415472](https://github.com/janhubicka/lean-kk/actions/runs/45405415472) | success |
| KK Track A raw old-seed maximal odd Bad budget | [45405415326](https://github.com/janhubicka/lean-kk/actions/runs/45405415326) | success |
| KK Track A/G automatically indexed odd Kpt Bad budget | [45405415234](https://github.com/janhubicka/lean-kk/actions/runs/45405415234) | success |

## Scope

The checked result is the finite actual-run exact-Plan theorem and its
full-age B3, structural, literal-table and selected-source components.
The ordinary resolved-Q application and small-independent proof have been
independently audited in English. The Lean constructor and event invariant,
record-to-slot parser, full lower history induction, enumeration and final
degree/characterisation composition remain work to be formalized. The
arbitrary finite graph / general K-ell characterisation is not promoted.

The final integrated-candidate review is appended to
`2026-11-24-complete-olive-characterisation-prose-audit.md`; the manuscript
publication checkpoint records the exact compiled source and preserved
pending markers. No global pending marker is made green by these CI results.
