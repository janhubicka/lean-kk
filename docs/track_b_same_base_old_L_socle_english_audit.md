# Track B — old ordinary-L prefix equality for ONE underlying numerical-Henson base
**14 November 2026. English-first proof and hostile review.**

## Problem

The physically complete Track B comparison between two separate Henson occurrences currently displays
`SameInitialL P.ambient.L Q.ambient.L cut`
as a genuine external hypothesis. This is unavoidable in full generality: two different base Henson graphs may have different ordinary-L atoms on their numbered initial prefixes, and equality of selected macrodiary graph-age data does not force their old-prefix equality.

However, in a *single chosen base Henson graph*, two different finite numerical-H presentations obtained by truncating the SAME numerical construction at possibly different finite heights have automatically equal complete old ordinary-L prefixes (when both contain the tested coordinate). This is a useful physical case for comparing two actual finite AlgorithmRuns over a common global E, without assuming their entire Kpt source closures or original name universes coincide.

## Theorem A — every finite numerical H prefix has the same old ordinary-L socle

Let `K : AgeTestModel db du dd`, `k,N1,N2,cut:Nat` with `cut<N1` and `cut<N2`. The finite numerical-H L-reduct constructor is defined as

```
finiteNumericHL K k N :=
  { carrier := {x : Nat | x < N},
    binary := hNumericBinary K.binary k,
    unary := hNumericSingleton K.unary k,
    diagonal := hNumericSingleton K.diagonal k }.
```

Only its *carrier* depends on N. All complete directed positive and negative binary relation bits, all unary bits and all diagonal bits are independent of the finite truncation parameter. Therefore
```
SameInitialL (finiteNumericHL K k N1)
             (finiteNumericHL K k N2) cut.
```

Proof of the four fields:
1. For every x≤cut, both x<N1 and x<N2; hence membership in the two carrier predicates is equivalent.
2. For x,y≤cut and each directed binary symbol, the expressions on both sides are *identically* `hNumericBinary K.binary k x y t`.
3. Unary expressions are identical `hNumericSingleton K.unary k x t`.
4. Diagonal expressions are identical `hNumericSingleton K.diagonal k x t`.
No claim about auxiliary E records or different source-coordinate cuts is needed.

## Theorem B — align two HensonCutOccurrence old L socles when they have the same E and k

Fix `P,Q : HensonCutOccurrence ell cut hell`. The occurrences may have different finite heights N, different true Kpt closures Z, original name maps and sets Full. Assume only that the literal underlying base graphs coincide (`P.E=Q.E`) and that the numerical generation parameter agrees (`P.k=Q.k`). Both contain cut by `P.hCut` and `Q.hCut`. Replace E and k in the second ambient by the first; apply Theorem A to
`K=normalizedGraphModel P.E`.
Conclude `SameInitialL P.ambient.L Q.ambient.L cut`.

This discharges ONE of the two missing inputs of the physical cross-occurrence corrected-B3 theorem in the common-base situation. No equality of arbitrary local full Kpt closures is implied.

## Theorem C — in a common base, the intrinsic cut-star profile alone controls B3 after source exhaustiveness

Suppose P and Q use the same base E and same k, and EACH has an actual complete/full source certificate of the kind proved in Track B PR #141:
`Full(v) ↔ closureSelectedOriginal(...)`, and every physical closure node lies under a named actual original in that occurrence. Suppose their **INTRINSIC** positive-cut physical Kpt crossing spectra agree at the same cut:
```
∀ R, PhysicalCutStarUpperL family P.Z cut R ↔
     PhysicalCutStarUpperL family Q.Z cut R.
```
Then theorem B supplies the old L-socle alignment, and PR #141's intrinsic physical cut-star cross-ambient theorem supplies
```
P.fullProfile.CorrectedB3 family ↔ Q.fullProfile.CorrectedB3 family.
```
This is a concrete reduction for two separate true finite runs over one fixed base Henson graph, retaining all their actual auxiliary original source participation. It does NOT assert that a selected diary establishes equality of the intrinsic spectra.

## Adversarial checks

1. The assumption `cut<N1,N2` is essential for carrier equivalence at x=cut; without it the initial socles can differ.
2. The second theorem requires **literal base graph E equality**, not just graph isomorphism or equal selected graph-age function.
3. The generation parameter k must match because the numerical `hNumericBinary` generation gates can differ otherwise.
4. The statement is about ordinary-L alone. The finite E relation is clipped to N and its source crossings depend on the constructed partial structure; equality of L does NOT imply equal auxiliary E/full Kpt source records.
5. Directed binary, absent binary, unary and diagonal relation bits are all preserved in Theorem A. No positive-edge-only shortcut.
6. Different original-name and Kpt-closure sizes are permitted. Same underlying base E and k do not imply equality of their full closure-selected cut-star spectra.
7. Different target numerical positions cannot simply be identified as the same source cut. Both physical occurrences must use the same integer source-coordinate cut.
8. The two-source B3 application requires full source EXHAUSTIVENESS in both occurrences, beyond the old one-sided `hRepresented`.
9. Full no-(I2) remains needed to treat the full crossing as a prescribed function; this theorem does not classify structural cuts.
10. At a true finite AlgorithmRun, source exhaustiveness follows from the maintained original pool invariant, not from matching base E.
11. The K4 q2 auxiliary cut-neighbour remains part of the physical spectrum; same base E does not make it a selected diary branch.
12. The normalized forbidden family may contain asymmetry and loop patterns; the HensonCutOccurrence physical hypotheses retain graph-loop-free and symmetry certificates.
13. Equality of intrinsic cut-star spectra is a condition on complete **upper** L-types, not merely the old prefixes or the number of cut-neighbour labels.
14. Cross-occurrence common labelled inverse-source orbit, event-indexed dependent E parameters and the relative-continuation corrected-B3-loss bridge remain open.
15. This does not establish the unbounded resolved diary, exact big Ramsey degree upper bound or independent lower bound; manuscript global validation remains pending.

## Strict gate

Commit English proof BEFORE Lean. Implement three named endpoints in `Kk/B3SameBaseOldSocle.lean`, import and register exact axiom checks. The current main baseline incorporates the three 547-report Track B source-certification endpoints, with separately stacked actual-run source completeness pending. Require full `lake build`, parser self-test and **550** named standard-only transitive-axiom reports on the exact PR head. This branch is independent of the actual-run stack.
