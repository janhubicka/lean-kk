# Whole-stage old-to-next coherence excludes the actual structural tests

## Status, inputs, and intended endpoint

This is a second English-first proof proposal, following
`positive_generation_stage_coherence_english_20261123.md`. Independent review,
parent approval, implementation, and kernel checking of this extension are
pending. The supplied positive-generation coherence result is itself to be
implemented only after its approved English proof and the canonical-generation
interface repair have been committed.

The main concrete endpoint is: at an omitted resolved-Q base b and a positive
lower generation `0 < g < k`, the actual current closure has neither an I1 node
at `c = hPosition k b g` nor an I2 meet at c, provided no initial seed ends at c,
the seeds have the stated actual root representation, and the actual stage
`J = Run.I (c+1)` satisfies the bounded role/Plan contracts from the first note.
The Plan inclusion remains an input. No final-pool identification, chosen B3
verdict, global boringness, completed omission induction, or orbit conclusion
is inferred from these structural statements.

The proof extracts the exact reusable reasoning already present in the zero
column results. Zero ordinary L is used in those results only to establish
complete old-to-next type coherence. The new positive-generation argument
establishes that same coherence by reading an actual old generation-zero
coordinate. The rest of the meet/fork argument is unchanged.

## Conventions and the exact coherence condition

Keep the existing graph language dimensions `1 0 1`. For an actual finite
`A : EnumeratedPartialStructure 1 0 1`, write

```
old(v)  := A.partialTypeAt c v.val
next(v) := A.partialTypeAt (c+1) v.val
eligible(v) := c+1 ≤ A.freeLevel v.val
```

These are complete dependent L+/E types, including negative ordinary atoms and
both auxiliary E directions. For a set `S : Set (Fin A.size)`, the precise
whole-original hypothesis is

```lean
hCoherent : ∀ v w : Fin A.size,
  v ∈ S → w ∈ S →
  c+1 ≤ A.freeLevel v.val → c+1 ≤ A.freeLevel w.val →
  A.partialTypeAt c v.val = A.partialTypeAt c w.val →
  A.partialTypeAt (c+1) v.val = A.partialTypeAt (c+1) w.val
```

For a named finite original pool `original : Fin M → Fin A.size`, the
corresponding condition quantifies over every `v w : Fin M`, with both genuine
eligibility premises and the same old-to-next implication for `original v`
and `original w`. It does not require injectivity of `original`, equality of
canonical ages, or a chosen-target reconstruction. It is a lemma hypothesis
only in the generic structural bridge; the concrete resolved-Q endpoint
discharges it with the actual-source proof from the first note.

## 1. Two actual eligible originals cannot meet exactly at c

Retain the data of `actual_zero_cut_originals_meet_level_ne_cut`:

- `family : List (NormalizedForbidden 1 0 1)`;
- A and `hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L`;
- `c : Nat`, `v w : Fin A.size`;
- the two genuine eligibility assumptions;
- `hComp : SameComponent (A.kptOriginal family hAvoid v)
  (A.kptOriginal family hAvoid w)`.

Replace symmetry and the two zero ordinary-bit assumptions by the pairwise
instance of coherence

```lean
hNext : A.partialTypeAt c v.val = A.partialTypeAt c w.val →
  A.partialTypeAt (c+1) v.val = A.partialTypeAt (c+1) w.val
```

Then the exact conclusion is

```lean
LevelTree.lev
  (LevelTree.meet
    (A.kptOriginal family hAvoid v)
    (A.kptOriginal family hAvoid w)) ≠ c
```

### Proof

Suppose the meet ends at c. Since both originals have level at least c+1, the
meet is their common ancestor at c. Their two ancestors at c+1 must differ:
if equal, that shared ancestor would be a common lower bound above their meet,
giving `c+1 ≤ c`.

Use `kptBelowOriginal_ancestor_raw` on each original at c. Equality of the raw
sigma nodes at that fixed level gives the displayed complete old-type equality
by `Sigma.mk.inj_iff` and `eq_of_heq`. Apply hNext. Use the same ancestor-raw
identification at c+1, and `Subtype.ext`, to conclude that the two next
ancestors are equal, contrary to the previous paragraph.

All tree arguments and all raw-type transports are literally the current
`Kk/TrackDZeroMeetObstruction.lean` proof. Its only zero-column call is replaced
by hNext. Symmetry is unnecessary in this generic bridge because any required
symmetry was already used to prove hNext. There is no hidden claim that either
original itself belongs to the current selected closure.

## 2. Whole-stage coherence excludes every full I1 terminal

Let `K : AgeTestModel 1 0 1`, `k N : Nat`, and `A := finiteNumericH K k N`.
Retain exactly the structural data of
`finiteNumericH_even_real_no_full_I1_of_zero_stage`:

- family and `hAvoid` for A;
- an arbitrary level set `I : Set Nat`;
- `X : Set (AdmissibleKptNode family)`;
- `U : Set (Fin A.size)`;
- `hSeeds : X ⊆ ambientPrefixPool family A hAvoid U`;
- `b g : Nat`, `c := hPosition k b g`, and `hPositive : 0 < c`;
- `hNoSeedAt : ¬ ∃ z, z ∈ X ∧ LevelTree.lev z = c`.

Put `S := ambientStagePool A U I`. Assume the exact whole-original hCoherent
above on S. The conclusion is

```lean
¬ ∃ z : AdmissibleKptNode family,
  z ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X ∧
  LevelTree.lev z = c
```

No symmetry, zero-column, no-I2, chosen B3, or AlgorithmRun assumption is
required at this generic level. The theorem is valid for an arbitrary I.
The actual AlgorithmRun application below fixes I to its literal current
stage instead of replacing it by an intended final set.

### Proof

Take a claimed closure node z at c. By hNoSeedAt it is not a seed.
`finiteNumericH_even_real_level_nonseed_is_original_meet` gives v,w in the
complete ambient stage pool S, a same-component proof for their actual
originals, and equality of z with their actual meet. The source theorem covers
all generated auxiliary-parameter and meet nodes; it does not assume selected
coding representatives.

The meet lies below each original, so `c ≤ A.freeLevel v.val` and the same for
w. Since c is positive, both free levels are positive. The verified theorem
`finiteNumericH_positive_freeLevel_ne_realPosition` says a positive free level
cannot equal this even real position. Hence both free levels are strictly
greater than c, giving the two required eligibility inequalities.

Apply the generic two-original meet obstruction from section 1 with
`hNext := hCoherent v w hv hw hFreeV hFreeW`. Its contradiction proves the
conclusion. This is why coherence on the whole original stage is needed:
the original-meet witnesses supplied by the normal form have not first been
shown to represent strictly crossing nodes of the smaller closure source.

The real-even and positivity gates are essential in this argument. It does
not apply at an arbitrary odd auxiliary cut, and positivity cannot be omitted
merely because the coordinate is even.

## 3. Exact source representation plus coherence excludes strict full forks

Let family, A, and hAvoid be as above, `original : Fin M → Fin A.size`, and
`Z : Set (AdmissibleKptNode family)`. Retain the exhaustive actual-source
representation premise

```lean
hPool : ∀ z : AdmissibleKptNode family, z ∈ Z →
  ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v)
```

Assume coherence for every pair of eligible names in original:

```lean
hCoherent : ∀ v w : Fin M,
  c+1 ≤ A.freeLevel (original v).val →
  c+1 ≤ A.freeLevel (original w).val →
  A.partialTypeAt c (original v).val =
    A.partialTypeAt c (original w).val →
  A.partialTypeAt (c+1) (original v).val =
    A.partialTypeAt (c+1) (original w).val
```

Then prove `¬ KptFullCutFork family Z c`. There is no no-I1 premise in this
strict-fork statement. This version of coherence deliberately covers all
eligible pool names, so the represented-name predicates in the zero theorem
are unnecessary as extra hypotheses. No representative is invented.

### Proof

A full fork supplies actual a,b in Z strictly above c, equal complete old raw
records, and unequal complete next raw records. Use hPool separately on these
same a,b to obtain va,vb and their below-original proofs. Since each crossing
node lies below its original, both originals are eligible.

`kptBelowOriginal_ancestor_raw` identifies the old ancestor of a with
`⟨c, A.partialTypeAt c (original va).val⟩`, and similarly for b. The definition
of full crossing records, through `kpt_full_old_upper_types_of_crossing`,
translates their old-record equality to equality of these two actual complete
old physical types. Apply hCoherent. Identifying both next ancestors at c+1
then gives equality of their complete upper records, contradicting the fork.

This is the proof of
`full_kpt_cut_fork_false_of_zero_full_physical_star` from
`Kk/TrackDZeroStarFullI2.lean`, replacing only its zero-column uniqueness call.
The representation of a and b must be by originals in one actual ambient A;
separate L-only shadow witnesses do not satisfy hPool.

## 4. No-I1 plus no strict full fork excludes all I2 tests

Under exactly the data and hypotheses of section 3, add

```lean
hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
  z ∈ Z ∧ LevelTree.lev z = c
```

Then prove

```lean
¬ ∃ a : AdmissibleKptNode family, a ∈ Z ∧
  ∃ b : AdmissibleKptNode family, b ∈ Z ∧
    SMTree.Envelope.SameComponent a b ∧
    LevelTree.lev (LevelTree.meet a b) = c
```

Indeed, `kpt_no_I1_I2_iff_complete_full_fork family Z c hNoI1` converts an I2
witness into a strict full fork, which section 3 excludes. This is the exact
existing no-I2 composition with the new coherence-based fork lemma.

The displayed I2 predicate allows `a = b`. A terminal z at c gives the trivial
meet `(z,z)` and need not give a strictly crossing fork. Therefore hNoI1 must
remain present in this generic implication. It is derived separately from
section 2 in the actual stage application, rather than silently dropped.

## 5. Finite whole-stage structural bundle

Use `U : Finset (Fin N)`, `I : Set Nat`, and the same A, family, hAvoid,
X, root representation, positive real c, and no-seed-at-c hypotheses. Put

```
Stage := hStageOriginals K k N U I
original := hOriginalName Stage
Z := closure (admissibleKptSTree family) I X
```

Assume the indexed whole-stage hCoherent of section 3 for this original.
Then both the no-I1 conclusion of section 2 for Z and the complete no-I2
conclusion of section 4 for Z hold.

### Proof and naming obligations

The finite Stage and `ambientStagePool A (U : Set (Fin N)) I` have precisely
the same members: unfolding their definitions gives
`v ∈ U ∨ (v.val ∈ I ∧ 0 < A.freeLevel v.val)`.
For each ambient member v, the actual index
`i := Stage.equivFin ⟨v,hv⟩` satisfies `hOriginalName Stage i = v` by the
definition of `hOriginalName` and the inverse laws of `equivFin`.
Use this exact equality twice to transfer indexed hCoherent to the membership
form required in section 2. This establishes no-I1.

For every z in Z,
`finiteNumericH_stage_closure_represented_by_stage_originals` supplies an
actual member v of the same Stage with `z ≤ A.kptOriginal family hAvoid v`.
The same `equivFin` naming produces the hPool required in section 3. This
source theorem has no no-I2 hypothesis, so there is no circularity. Apply
sections 3 and 4 to obtain no-I2.

Both naming steps are already implemented in
`finiteNumericH_run_stage_and_final_pool_exhaust_same_closure`, but the direct
arbitrary-I construction here avoids using its final-pool conclusion. The
normal form used for I1 and the representative pool used for I2 are both the
complete true current stage. No injectivity on types is needed.

## 6. Actual positive-generation resolved-Q AlgorithmRun endpoint

Fix the following actual data:

- `family : List (NormalizedForbidden 1 0 1)`;
- `E : Nat → Nat → Bool`, `K := normalizedGraphModel E`, `k N : Nat`,
  `A := finiteNumericH K k N`;
- `hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L`;
- `U : Finset (Fin N)`, `X : Set (AdmissibleKptNode family)`, and
  `hX : X ⊆ ambientPrefixPool family A hAvoid (U : Set (Fin N))`;
- `top : Nat` and an actual
  `Run : AlgorithmRun (normalizedKptSMTree family) X top`;
- `b g : Nat`, `hg0 : 0 < g`, `hg : g < k`, and
  `hCut : hPosition k b g < N`;
- `c := hPosition k b g`, `J := Run.I (c+1)`;
- `hNoSeedAt : ¬ ∃ z, z ∈ X ∧ LevelTree.lev z = c`;
- `Plan : Set Nat`, `hAbove : J ⊆ Plan`, role and
  `hQ : ResolvedQChronologicalAxioms role E`;
- the two **bounded-generation** root and Plan contracts, with `m ≤ k`
  explicitly present, exactly as in the first English note;
- `hOmitted : ResolvedQOmittedBase (role b)`.

The exact conclusion is the conjunction

```lean
(¬ ∃ z : AdmissibleKptNode family,
  z ∈ SMTree.Envelope.closure (admissibleKptSTree family) J X ∧
  LevelTree.lev z = c) ∧
(¬ ∃ a : AdmissibleKptNode family,
  a ∈ SMTree.Envelope.closure (admissibleKptSTree family) J X ∧
  ∃ b' : AdmissibleKptNode family,
    b' ∈ SMTree.Envelope.closure (admissibleKptSTree family) J X ∧
    SMTree.Envelope.SameComponent a b' ∧
    LevelTree.lev (LevelTree.meet a b') = c)
```

The structural conclusion only uses the actual stage set J of Run. A bound
`c < top` and a top seed witness are needed when composing this with the
existing actual-run nonselection theorem, as stated in section 8. They are
not used by the arbitrary-I structural proof and must not be purportedly
derived from it.

### Proof

The first English note gives complete old-to-next coherence for every pair
of genuinely eligible names in `hStageOriginals K k N U J`. Its proof uses
the actual higher-stage inclusion hAbove and the bounded root/Plan contracts;
it does not assume a structural conclusion or substitute a selected tuple.
The literal address formula and `0 < g` give `0 < c`. Supply this coherence,
positivity, root representation, and hNoSeedAt to the bundle in section 5.
The resulting conjunction is the displayed conclusion.

No selected independence hypothesis is needed for this positive-generation
structural endpoint. The omitted-base role axioms force positive eligible
stage neighbours to selected TOPs, and the old coordinate already determines
their ordinary cut bit. Block convexity is also unnecessary for this case.

## 7. Concrete TOP-generation seeds discharge the seed premise

For a concrete application take `cap : Fin N`, `blocks : Finset Nat`, and

```lean
hWithin : ∀ i : Nat, i ∈ blocks →
  hPosition k i k ≤ A.freeLevel cap.val
```

Let `U := {cap}`, `top := A.freeLevel cap.val`, and

```
X := numericHTopGenerationSeeds family K k N hAvoid cap blocks hWithin
```

Use an actual Run on that exact X and top, and retain every bounded role/Plan,
cut-bound, and omitted-role hypothesis from section 6. The one-cap bounded
root contract lifts to U by singleton membership. The existing
`numericHTopGenerationSeeds_subset_rootPool` supplies hX.
`numericHTopGenerationSeeds_noPositiveLowerReal`, with `g < k` and the
derived `0 < c`, supplies hNoSeedAt. Thus section 6 proves the full no-I1/no-I2
conjunction for this literal seed family without a separate seed-absence
assumption. It does not by itself prove that Run skips c.

The cap original belongs to X and supplies the top seed witness if the
conditional nonselection composition below is used. The hypothesis `c < top`
must still be retained there. Positivity of c alone does not imply it.

## 8. Optional conditional nonselection composition; the age gate remains

For the Henson actual-run specialization retain all nonstructural input data
of `henson_actualRun_lower_real_unselected_of_planned_stage_markedB3`:

- `ell`, `hell : 2 ≤ ell`, and `hK : ell ≤ k+1`;
- actual E looplessness, symmetry, and the displayed increasing-ell-clique
  exclusion;
- N, U, hAvoidA, X, hX, top, the actual Run, and
  `hTop : ∃ x ∈ X, LevelTree.lev x = top`;
- the two cut bounds `c < top` and `c < N`, plus `0 < g < k`;
- actual stage inclusion `Run.I (c+1) ⊆ Plan`, omitted base role, hQ, and
  the repaired bounded root/Plan contracts;
- no initial seed ends at c, unless section 7 supplies that fact.

Define exactly the same Stage, original, Z, Full, and Marked as that existing
theorem, with

```
Full := closureSelectedOriginal family A hAvoidA original Z c
Marked := resolvedQStageSelectedTopMarked role k Stage Full
```

The remaining supplied implication is

```lean
(selectedStagePoolPrescribedData A c original Marked).CorrectedB3 family →
  c ∉ Run.I 0
```

To prove it, derive hNoI1 and hNoI2 by section 6, derive `0 < c` from `0 < g`,
and invoke the **bounded-contract repaired version** of the existing actual
planned-stage marked-B3 nonselection theorem. All required base coverage is
then provided by its bounded positive-TOP helper. The actual chosen Marked
corrected-B3 premise remains explicit; old-to-next coherence alone does not
establish that age verdict. This is a local conditional corollary, not a proof
of full global B3 or of the descending Plan hypothesis.

## Adversarial review checklist

1. Complete physical old/next dependent types are used at every equality;
   neither positive adjacency alone nor equality of ages can replace them.
2. The generic meet bridge retains both eligibility inequalities and actual
   same-component originals in one ambient A.
3. I1 normal-form witnesses are in the complete ambient stage, which is why
   the coherence input must cover more than marked crossing representatives.
4. No seed at c remains explicit until the exact TOP-seed theorem discharges
   it for the literal seed family.
5. Positivity of the real cut is supplied before positive free-level parity
   is used; the g=0 boundary is outside the new concrete coherence theorem.
6. A level bound `c ≤ freeLevel` is strengthened to eligibility using actual
   positive-free-level parity, not address order alone.
7. hPool covers every node of the actual Z, including all generated E and
   meet nodes; no selected-shadow source substitutes for it.
8. Both old and upper names of a crossing node use the same physical original
   representative and the same below-original proof.
9. No-I1 remains necessary for no-fork to imply no-I2, since self-meets at c
   satisfy the I2 predicate.
10. Stage membership and its finite enumeration are connected through actual
    `equivFin` inverse equality, not merely equal partial types.
11. The arbitrary-I representation theorem has no no-I2 premise, so source
    coverage is obtained before the structural conclusion.
12. J is literally `Run.I (c+1)` in the actual-run endpoint. No equality with
    `Run.I 0`, final Plan, or a selected terminal tuple is assumed.
13. Every root/Plan address contract has the canonical `m ≤ k` guard; the
    old unbounded compatibility interface must not re-enter the application.
14. The optional skip composition retains top seed, strict c<top, finite
    cut bound, Henson hypotheses, and the actual chosen corrected-B3 input.
15. No no-I3, global omission induction, retained-role realization, or common
    labelled source conclusion is attributed to the structural bundle.

