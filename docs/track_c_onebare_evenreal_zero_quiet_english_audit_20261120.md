# Track C — one bare numerical-H+ root: full quietness at a positive even-real old-boring zero cut

20 November 2026. English-first proof and adversarial audit. New Lean endpoint NOT kernel-verified until the exact-head gate passes.

## Actual finite geometric assertion

Let `A=finiteNumericH K k N` for the graph signature (one ordinary symmetric binary relation, no unary relation, one diagonal relation), forbidden family `family`, and true old Kpt AlgorithmRun `R` on possibly dependent Kpt seeds `X`, with old top `top`. Pick ONE genuine original coordinate `newV : Fin N`, and form the bare source `Y = X ∪ {A.kptOriginal family hAvoid newV}`, not a set of all ancestral prefixes and not the inherited final-closure seed set.

Fix a positive even-real cut `c=hPosition k idx g` with `c<top` and `c∉R.I c`. Require that Y is genuinely represented by a complete physical `ambientPrefixPool` on a finite original support U. For the actual old selected tail `R.I(c+1)`, assume:

(Z) Every eligible genuine stage original v which crosses c has ordinary L(c,v)=false; the full ORIGINAL stage pool includes reserved/coding/gap originals, not only selected graph vertices.

(P) For every actual stage original v that represents some NEW crossing closure node z≤O_v, there exists an OLD LIVE closure node w with exactly the same complete old Kpt `ancestor_c(O_v)=ancestor_c(w)`. Here the old prefix includes ALL dependent ordinary L and auxiliary E data. No new-level upper type equality is independently assumed.

Then the *entire new candidate pre-cut source* `closure_(R.I(c+1))(Y)` is quiet relative to the old pre-cut source `closure_(R.I(c+1))(X)`: no full I1 terminal at c, and EVERY complete old/upper Kpt L+/E crossing pair of a NEW node is realized by a SAME old node. Formally `NewRootNoNoveltyAtCut family oldSource candidateSource c`.

## English proof

(1) Since c is omitted by the GENUINE old AlgorithmRun, the old run's interesting-step axiom makes the pre-cut old source genuinely boring. The verified E76 theorem, applying to arbitrary legitimate dependent initial seeds X, shows no seed of `X∪{O_new}` ends at the positive real c. This is the crucial correction to the invalid assumption that X comprises only literal originals.

(2) The full zero-column hypothesis (Z) on the true finite stage originals is also the zero-column premise on D389's `ambientStagePool A U (R.I(c+1))`: these are extensionally the same original-name pool, with one side represented by `hStageOriginals` and the other by `ambientStagePool` (the conversion is a transparent Finset membership calculation, with carrier size N). Together with genuine ambient ordinary-L symmetry and (1), D389 excludes ALL I1 terminals of the candidate meet/parameter closure, not just original-root terminals. The positivity and even-real coordinates are essential.

(3) Given the original-prefix hypothesis (P), E74's verified `finiteNumericH_candidate_zero_stage_original_prefixes_cover_full_crossings` supplies inclusion of the complete candidate old/upper L+/E crossing relation in the old relation. Its proof uses physical original representatives for EVERY generated meet or parameter Kpt node and the exact zero-column rigidity to transport all upper E bits. No no-I2 condition, prefix-shadow projection, or selected graph-age comparison is used.

(4) Combine (2) and (3), which are exactly the two conjuncts of `NewRootNoNoveltyAtCut`.

## Hostile audit / exact scope

1. This theorem proves ACTUAL complete source no-novelty at one cut, not merely another iff between unverified quietness tests.
2. Hypotheses Z and P are genuinely geometric and remain to be checked for the intended resolved diary; they are **not** consequences of old-boringness alone.
3. Only ONE new bare original O_new is adjoined to arbitrary old dependent seeds. The all-ancestor initial seed pool would create spurious I1 terminals and INVALIDATE step (1).
4. The target is candidate closure under the OLD selected tail R.I(c+1). This is NOT the independently computed pre-cut closure of a new AlgorithmRun Rnew; one must separately transport actual run choices to infer a statement about Rnew.
5. The cut is a *positive even-real* H+ coordinate, not an odd E-free cut, fake cut, or arbitrary natural level. In particular auxiliary K4 q2 cuts 10 and 22 must be analyzed according to their TRUE physical source roles, not discarded because they are even numbers.
6. The original L symmetry is required only for ordinary graph bits; directed auxiliary E is never symmetrized.
7. P matches full admissible Kpt old ancestors, including E and negative L bits; comparing mere graph neighborhoods or canonical graph age is insufficient.
8. The single old witness w must realize BOTH the old and upper complete crossing pair. E74 provides this after physical zero-stage rigidity; no independent matching of old and upper vertices is allowed.
9. Full stage pool Z includes all eligible original coordinates, not only retained/marked vertices. Omitting gap originals is unsound.
10. The seed exclusion is not a postulated 'no I1' hypothesis: it follows from real old-boringness and parity for ONE genuine new original. The generated meet/parameter I1 exclusion is separately proved by D389.
11. No source-node count, uniform microevent budget, global cut-coordinate normalization, common inverse source monoid orbit or BRD equality is implied.
12. Y remains a represented physical source, so the bare-root choice does not allow arbitrary unrepresented Kpt nodes.
13. The old run R must be a real AlgorithmRun, not merely an arbitrary selected-level mask; the E76 argument uses the actual interesting-step axiom.
14. If zero original stage columns or full original-prefix matching fail, a novel dependent auxiliary E pair may appear; the conclusion is then not asserted.
15. Existing E73 PR #394 has an overlapping candidate theorem under an ASSUMED no-Y-seed condition and full socle coverage; this independent C proof strengthens that route by deriving no-Y-seed and reducing socle checks to ORIGINAL representatives. It must not be used as a source dependency while #394 remains unmerged/only partially CI verified.
16. Do not promote this to a manuscript GREEN/BLUE mark unless exact-head Lean build and named transitive-axiom audit both pass; even then the global diary application stays PENDING.

## Verification and editorial plan

Create a standalone `Kk/TrackCOneBareEvenRealZeroQuiet.lean`, import only the MERGED E76, D389 and E74 sources, prove the claim from the actual physical hypotheses, and expose the theorem in a named exact axiom audit. Avoid edits to frozen black manuscript text. After verification, annotate a concise OLIVE checkpoint preserving existing TODO decisions.
