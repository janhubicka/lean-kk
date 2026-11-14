# KK-free Track B — certify that the alleged FULL source is exhaustive
**14 November 2026 — English mathematical proof and adversarial audit. This note is committed BEFORE Lean.**

## Critical audit correction

The merged cross-ambient interface `Kk.HensonCutOccurrence` contains:
- `Full : Fin M → Prop`, a name-selection predicate;
- `hRepresented : ∀ v, Full v → closureSelectedOriginal ... Z cut v`.

**This is only one-sided inclusion**. It does NOT require that every name representing a true crossing belongs to `Full`, nor that the supplied original-name map covers every actual Kpt closure node. The two cross-ambient B3 theorems are valid conditional theorems about these selected-source profiles, but **one cannot instantiate them as the manuscript's FULL parameter-closed Algorithm 5.4 source from the existing `HensonCutOccurrence` hypotheses alone**.

For a truly complete stage, we need BOTH:
1. **Exact name selection** `Full(v) ↔ closureSelectedOriginal family A hAvoid original Z cut v` for every finite name.
2. **Exhaustive closure pool** every actual `z∈Z` is a prefix of an original in the fixed finite name pool.

The previous Track C numerical-H final-stage invariant already proves (2) from a genuine AlgorithmRun seeded in actual ambient originals, and (1) can be imposed definitionally by choosing `Full := closureSelectedOriginal`. We must keep both visible in the audit and formal source-graph bridge.

## Theorem A: exact physical FULL source-graph certification

For `P : HensonCutOccurrence ell cut hell`, assume the two obligations above. Let
`F = P.fullProfile = selectedStagePoolPrescribedData P.ambient cut P.original P.Full`.

By extensionality of name predicates, the exact-selection hypothesis identifies `P.Full` with the canonical `closureSelectedOriginal`. Consequently `F` is **definitionally the chosen** `closureSelectedBoringData family P.ambient P.hAvoid P.original P.Z cut`.

Use the already verified Track C/E theorem
`finiteNumericH_full_crossing_graph_is_physical_relation` on P's finite numerical-H model, *exhaustive* pool and full no-(I2) hypothesis. It proves precisely
```
fullPrescribedCrossingGraph F =
FullPhysicalClosureCrossing family P.Z cut.
```
This is equality of the complete OLD+UPPER **L+** crossing relation of the actual closure, not only equality of L-reduct spectra or graph-age bounds. Every genuine crossing appears and no extraneous crossing is introduced.

**Adversarial test:** with an arbitrary proper subset `Full`, `hRepresented` still holds but the equality above can fail, and corrected B3 of the alleged full source may be vacuously true. Therefore exact-selection AND exhaustive-pool obligations must be displayed and never replaced by a one-sided representation condition.

## Define a pool-independent PHYSICAL cut-star invariant

For one actual Kpt closure `Z` at source cut `c`, define the complete ordinary-L cut-star spectrum
```
PhysicalCutStarUpperL family Z c R
  :↔ ∃ T U,
      (T,U)∈FullPhysicalClosureCrossing family Z c
      ∧ U.lReduct = R
      ∧ R.binary (some (Fin.last c)) none 0 = true.
```
Here `R : RelationalPrefixType (c+1) 1 0 1`. The positive **ordinary-L** cut-to-upper edge is read directly from the complete next-cut L-reduct `R`; it is *not* a positive auxiliary E bit. The relation `FullPhysicalClosureCrossing` comes from real Kpt ancestors, independently of original-name pool, source representative selection, or chosen values outside a prescribed source.

## Theorem B: exact agreement of intrinsic physical spectrum and cut-star permitted types

Retain Theorem A's two completeness certificates and the actual no-(I2) hypothesis. Show:
```
P.starProfile.PrescribedUpperLType R
  ↔ PhysicalCutStarUpperL family P.Z cut R.
```

**Forward:** from a chosen star source `S`, extract the actual selected name `v` that the prescribed function uses via `selectedStagePoolPrescribedData_source_original`. Because `P.starNames v` entails `P.Full v`, `P.hRepresented` supplies a genuine closure node `z∈Z`, crossing c, that is a Kpt prefix of `P.original v`. The two checked `kptBelowOriginal_ancestor_raw` equalities exhibit
`(P.ambient.partialTypeAt c (original v), P.ambient.partialTypeAt (c+1) (original v))`
in `FullPhysicalClosureCrossing`. The chosen target has exactly the second complete L+ type. Finally, the star's positive physical edge equals the corresponding entry of the upper ordinary-L reduct via `partialTypeAt_lReduct_eq_ofAgeModel`. This yields the intrinsic physical cut-star predicate. No candidate upper--upper edges of a B3 test W are copied from the physical graph.

**Reverse:** from the intrinsic physical witness `(T,U)`, use Theorem A's exact physical-graph equality to get `T∈P.fullProfile.source` and `P.fullProfile.target T=U`. The real chosen-full-source original theorem supplies `v` with `P.Full v`, eligible cut and real next L+ type U. The positive ordinary-L cut edge read from `U.lReduct` makes v a genuine `P.starNames` original. Crucially, `Kk.HensonCutOccurrence.star_name_complete_upperL_permitted`—using actual no-(I2) fibre coherence—proves that THIS name's own full next L-reduct is permitted by the chosen star source, regardless of duplicates of its old L+ type. Thus R is permitted by P.starProfile.

No nonempty-star assumption is used: if there are no physical cut-adjacent crossings, both predicates are empty.

## Theorem C: between TWO exhaustive physical occurrences, comparing only intrinsic source-crossing projections suffices for B3

Let `P,Q : HensonCutOccurrence ell cut hell` each satisfy exact-selection and exhaustive-pool certificates (independently). Suppose their *actual old ordinary-L socles* align:
```
SameInitialL P.ambient.L Q.ambient.L cut.
```
Suppose the two intrinsic physical spectra agree for every complete next-cut reduct:
```
∀ R, PhysicalCutStarUpperL family P.Z cut R
      ↔ PhysicalCutStarUpperL family Q.Z cut R.
```
Apply Theorem B for P and Q to obtain equality of the permitted cut-star upper-L predicates. Apply the previously kernel-checked cross-ambient B3 theorem. Conclude:
```
P.fullProfile.CorrectedB3 family ↔
Q.fullProfile.CorrectedB3 family.
```

Unlike the prior name-matching theorem, this criterion compares **a projection of the canonical full physical closure crossing relation**, which Track E already constructs and indexes from real Kpt nodes and exact per-cut masks. It is therefore independent of the noncanonical choice of original-name pool or selected target representative. This is a genuine interface toward an event-indexed diary invariant; the diary-specific equality of the intrinsic spectra remains UNPROVED.

## Theorem D (actual run certification, if Lean interface permits)

Take a genuine finite numerical-Henson `AlgorithmRun`, seed-prefix set `X⊆ambientPrefixPool ... U`, and a no-(I2) cut `c<top`. Use exactly the final maintained original pool
`V=hStageOriginals ... U (Run.I 0)`
and source `Z=closure ... (Run.I(c+1)) X`.

Set `Full := closureSelectedOriginal family A hAvoidA (hOriginalName V) Z c`. The exact-name condition is then literal reflexivity. The Track C theorem `numericH_algorithmRun_closure_original_in_final_pool` supplies the exhaustive-pool condition with actual names in V; no unverified source representation premise is left. Apply Theorem A to conclude that the **actual full AlgorithmRun** chosen crossing graph coincides with the canonical physical relation, with complete OLD and UPPER L+ records, and then Theorem B for the intrinsic finite B3 spectrum. This is still a *single real stage*, not a uniform source across different diary occurrences.

## Hostile review: 19 pitfalls to exclude

1. The previous `hRepresented` is **only one direction**. Do not call an arbitrary selected subpool an exhaustive FULL AlgorithmRun source.
2. Mere equality of selected graph-age F does not imply exact Kpt source-name selection or exhaustive Kpt parameter/meet closure.
3. Exact selection `Full ↔ closureSelectedOriginal` and exhaustive `hPool` are independent; neither implies the other.
4. `FullPhysicalClosureCrossing` records entire OLD+UPPER L+ `PartialTypeWithE` values. The projected spectrum deliberately forgets E only after physical source records exist.
5. The intrinsic projection tests the true ordinary-L bit at the tested cut; an incoming E bit is not an ordinary L edge.
6. The source cut has a FIXED integer coordinate c, required by all `PartialTypeWithE c` and `RelationalPrefixType (c+1)` types. Cross-occurrence cut reindexing is not automatically supplied.
7. The whole physical source may have an (I2) fork; a single prescribed function does not then cover both upper branches. The theorem keeps no-(I2) in each physical stage.
8. The star can be EMPTY and the intrinsic physical cut-star spectrum also empty. Do not fabricate an anchor.
9. A star name's actual next L-reduct may differ from the arbitrarily chosen next reduct of its old source in an *unconstrained* pool; the theorem uses actual closure representation and no-(I2) to prove fibre coherence.
10. Carrier, both directed binary, unary and diagonal atoms are preserved by the old L-socle condition. It is stronger than graph-age equality.
11. Arbitrary B3-witness upper--upper edges are freely chosen; no physical ambient future--future edge is transported.
12. `FullPhysicalClosureCrossing` is independent of the chosen original name enumeration, and the new physical cut-star spectrum inherits this independence.
13. The resulting matching condition is strictly weaker than equality of whole FULL physical L+ crossing relations in Track E, but still stronger than selected macrodiary F equality.
14. Equality of *sets* of intrinsic spectra does NOT imply equal finite named parameter index size or a common labelled monoid orbit.
15. The K4 q2/x auxiliary cut-10 counterexample is preserved: q2 must contribute its physical cut-star type if it lies in the true full closure and is L-adjacent.
16. The actual run source uses `Run.I(c+1)` while its maintained finite name carrier uses `Run.I 0`; do not swap them.
17. This repair does not establish that any proposed canonical resolved diary synchronizes physical old-prefix socles and intrinsic cut-star spectra across occurrences.
18. The full relative-continuation corrected-(B3)-loss equivalence remains separate and unverified by a finite B3 truth-value comparison.
19. No unconditional K_ell-free big Ramsey degree, exact diary count, independent lower bound or common labelled source orbit follows. Do not promote global manuscript GREEN.

## Strict Lean gate

Commit this English argument first, then implement and test the endpoint theorems in `Kk/B3FullSourceCertification.lean` (and optionally a separate actual-run module). Current main at this audit begins with `b93d5fe1c5cd421a9202b3b0607683308587e426` and has a full hosted Lean success [run 43593027416](https://github.com/janhubicka/lean-kk/actions/runs/43593027416). The ordinary central registry was at 544 reports before further Track G integration; CHECK the exact current count at merge time. Require exact-head `lake build`, parser self-test and all newly named only-standard transitive-axiom reports, and verify final merged Git tree equals tested tree. Keep the paper's global marker pending.
