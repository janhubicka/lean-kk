# Track F — central integration of independently verified independent-code components

21 November 2026. Source-only integration on top of independently exact-head verified and merged Lean PRs #424, #430, #433, #436, #438. The frozen black manuscript proof and global history/BRD pending markers are unchanged.

## Why integrate

Each named theorem was separately compiled in a dedicated exact-head module and checked by strict standard-only `#print axioms` reports. The central `Kk.lean` module and `scripts/check_axioms.lean` have not yet imported/registered these new components. Integrating them guards against loss of coverage in subsequent Track F history work and ensures any public type/signature drift is caught by the full project CI.

## Exact imports and theorem endpoints

- `Kk.TrackFActualIndependentCode` (#424): three endpoints: rank-preserving source zero padding avoiding finite coded past; genuine actual future fibre coding vertex with source+target two-way zero columns; rank-zero independent-code specialisation.
- `Kk.TrackFZeroCodePreprofileRigidity` (#430): one endpoint: complete pre-code profile equality from legitimate zero-code law, actual integer-age monotonicity, survivor agreement, and singleton rank one.
- `Kk.TrackFZeroCodeSurvivorSynchronization` (#433): two endpoints: target prefix zero bit forced by actual source coding fibre; genuine synchronized K4 survivor fronts after a code with full class preservation and target zero.
- `Kk.TrackFActualFrontCanonicalAge` (#436): two endpoints: actual safe one-types imply positivity of every RAW support and genuine canonical integer graph age.
- `Kk.TrackFTypePrefixCanonicalAgeSandwich` (#438): four endpoints: canonicalizer monotonicity, raw age antitonicity under true chronological refinement, complete canonical age antitonicity, and no-hidden-event three-front sandwich.

**Total: 12 new exact qualified named axiom checks.** All should report only `propext`, `Classical.choice`, `Quot.sound` or fewer. The existing main checks are not removed or changed.

## Scope

These components establish **local geometry, complete integer-age algebra and source/target front interfaces** for an independent-code event. They do NOT yet construct the actual immediate pre-code target tuple, prove its survivor-age equality to the later checkpoint, or identify the immediate post-code target profile. They do not realize cover/split operations or prove the direct lower bound or full diary characterization.

## Validation gates

Run the complete `lake build Kk` and the existing full strict `scripts/check_axioms.lean` parser against the resulting HEAD. Check the standard-only axiom parser's negative self-test. No manuscript green mark is permitted for the global history-realization proposition.
