# Track C — construct BOTH genuine bare/full new-root runs and compare their complete source

17 November 2026. **English FIRST, adversarial proof audit BEFORE Lean.**
Issue: [KK Track C #25](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/issues/25).
Baseline: merged \`lean-kk\` main a69aff48f0c6ab826d861e5b8ce1f7b07782fa71.

## Precise geometric input

Let K and L be genuine finite old/new base age-test models, k>0 a fixed
numerical-H+ generation height, b an old base-original cutoff, N≤M
old/new real numerical carrier sizes, and j>0 a new physical base
original. Put

  w = hPosition k j k : Fin M,
  T = hPosition k (j-1) k + 1.

Assume exactly the old/full constructors' physical hypotheses:

1. N≤M and N≤hPosition k b 0;
2. physical new top position hPosition k j k<M and N≤T;
3. K and L have **equal old binary, unary, and diagonal atoms**
   below base frontier b (BOTH directions, including false atoms);
4. the entire old and new finite numerical-H+ ordinary reducts
   avoid the normalized forbidden family;
5. old initial Kpt seeds X are genuinely represented by one
   old physical original-prefix pool U;
6. \`HasPhysicalExhaustiveKptRun family X oldTop\`: one ACTUAL
   old AlgorithmRun, a *REAL old top seed*, and one precise
   finite named full Kpt closure index with per-cut live masks.

Crucially, these are **input physical realizability requirements**;
the construction does not prove any new base graph extension can
meet them for every prescribed diary cover. Track A/B must supply
the genuine K-free/old-column stage for that infinite recursion.

## The next theorem (not assuming either new run)

Put \`O={KptOriginal_L(w)}\`,
\`Ybare = X ∪ O\`, and
\`Yfull = closure_(Rold.I0)(X) ∪ O\`.
Both next AlgorithmRuns scan the **same** top T, not
arbitrary unrelated tops.

The already checked constructors give:

- \`finiteNumericH_bareTopRoot_construct_exhaustive_run\` with
  inherited-level argument \`I=Rold.I0\`:
  \`Ybare⊆levelLe(T)\`, a TRUE \`Rbare\` at T, one top seed,
  and an exhaustive FINITE full Kpt source index + Boolean live mask.
- \`finiteNumericH_baseExtension_actual_top_root_run_bounded\`
  with \`I=Rold.I0\`:
  \`Yfull⊆levelLe(T)\`, a TRUE \`Rfull\` at T, top seed, and
  a separate exhaustive finite source index/live mask.

The old source's **physical** top seed and prefix coverage imply
\`oldTop≤T\` by
\`finiteNumericH_old_physical_top_le_new_chronological_top\`;
this is NOT an assumption of equality or a formal topI marker.

Then the newly **MERGED and exact-head checked** results prove:

- \`finiteNumericH_bare_and_full_new_runs_same_selected_levels\`
  (Track C #240):
  \`∀i≤T, Rbare.I(i)=Rfull.I(i)\`.
- \`finiteNumericH_bare_full_runs_final_source_eq\`
  (Track C #251): literally
  \`closure_(Rbare.I0)(Ybare)=closure_(Rfull.I0)(Yfull)\`.
- \`finiteNumericH_bare_full_runs_all_cut_events_eq\`
  (Track C #251): for every c<T, exact equality
  of I1, I2, genuine I3 skip-map decision and the FULL
  choice-free old/upper L+/E crossing relation, including
  fake coordinates, negative atoms, and repeated I2 outputs.

The final common source can use the bare run's **already
constructed finite named index**: if \`paramsBare\` represents
exactly the bare final closure, source equality makes it
represent exactly the full final closure as well. It does NOT
require an artificial bijection between unrelated enumerations.

## Lean deliverables

First theorem, **physical one-step pair**, concludes existence of
Rold, Rbare, Rfull with selected-I equality and literal final
full Kpt-source equality, using only constructor hypotheses.
Theorem should preserve the two genuine run witnesses, not
assert merely that preselected runs satisfy an implication.

Second theorem, **one common finite source index**, returns the
same actual Rold, Rbare, Rfull together with a Finset of complete
Kpt source nodes and one Boolean \`live\` mask. The Finset lists
EVERY node in both full final closures, injectively via
\`params.equivFin\`; for the bare run its live mask is EXACT at
all cuts, and for the full run at cut c it is EXACT for every
node of level≥c (not below c). The complete I1/I2/I3 and
choice-free L+/E event relations are equal at each cut.
This is stronger than a numerical count or untyped source-code
bag, while never inferring equality of raw low-stage masks.

The actual Kpt original pool O is **ONLY one new original**;
never use all ancestors of that original as initial seeds.
Those ancestors are a *covering pool*, and seeding them directly
forces I1 at all lower levels.

## Adversarial acceptance checks

1. The two actual numeric H+ models K,L can differ on NEW
   base vertices; equality is required only below b, but
   is COMPLETE there (two directions, negative L and unary/diagonal).
2. The forbidden-family avoidance of BOTH entire physical
   structures is required; no selected-front graph-age estimate
   substitutes for it.
3. The fresh original must be actually present at position w
   and have its real numerical E free cut T. No invented top.
4. The old top seed is part of the actual old physical run
   certificate; \`oldTop≤T\` follows from representation and N≤T.
5. If old I0 includes level 0, the argument still works: we
   use #240/#251, not the obsolete all-old-levels-above-c hypothesis.
6. If old X contains legitimate dependent parameters, those
   remain in the old initial seed X; **only the NEW original**
   is not pre-closed in Ybare.
7. The original-prefix cover U may include fake/auxiliary
   prefixes; it is a representation certificate, not a source
   of extra initial seeds.
8. The source index from the bare run is a genuinely finite
   list of *nodes* rather than just ordinary L profiles;
   all their assigned E and dependent upper types are intrinsic.
9. A single source set can have different true per-cut live
   masks under two seeds: claim equality only at/above c.
10. Do not assert the chosen monoid maps F_i coincide; their
    shapes can be different even with identical selected I_i.
11. Preserve the real K4 auxiliary cuts 10 and 22 whenever
    a true run selects them.
12. Both new runs scan EXACTLY T; no comparison of different
    new tops is claimed.
13. The proof is in ONE normalized Kpt successor tree;
    genuine different-occurrence coordinate transport is
    not supplied.
14. The output still depends on old input \`hSeeds\`, full
    avoidance and original-column hypotheses. An unbounded
    construction needs them at every stage.
15. Complete source and full crossing agreement is an
    *event-data* comparison, not full relative-(B3)-loss
    equivalence on selected graph-age continuations.
16. The finite index cardinality depends on the actual
    physical cut. It does NOT prove a uniform finite
    labelled envelope carrier across all occurrences.
17. A new original ancestor-prefix initial seed pool would
    force every level interesting by I1; it is forbidden.
18. No common labelled inverse-source monoid orbit, no
    unavoidability and no exact big Ramsey degree follows.

## Workflow

Create one independent Track C Lean module and two source-exact
named theorem checks. Prove English statement first (this note),
then formalize, require isolated exact-head Lake build and
standard-only transitive axiom audit, plus normal full repository
CI. Do NOT mark any manuscript claim green until both gates
actually pass. No black manuscript changes, no de-frozen TODOs,
no selected-shadow route resurrection.
