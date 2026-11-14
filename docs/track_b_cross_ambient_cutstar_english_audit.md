# Track B — cross-ambient corrected-(B3) transport by exact cut-star profiles
**14 November 2026. English proof and adversarial review committed BEFORE Lean.**

## Where this advances the paper

At the last checkpoint, Track B established the necessary physical cut-neighbour at a genuine nonstructural I3 event and an exact anchored cut-star reduction. Independent Track D subsequently improved this to an **anchor-free** normal form, including the empty source, and Track G registered both new theorems in the combined 535-report kernel-checked Lean gate. All these comparisons still occurred inside **one** numerical-H ambient.

The outstanding graph-specific diary task compares **different finite source presentations / occurrences**. We now isolate the *correct inter-ambient statement*: once the lower old ordinary-L socles are aligned on the source cut, equality of the full cut-star **complete next-cut ordinary-L reduct predicates** implies equality of the full corrected-(B3) truth values, even when the original-name universes, ambient Henson edge relations, selected pools, auxiliary E records and Kpt closure sets differ.

This does **not** prove that a proposed canonical diary actually synchronizes these two pieces of data. It sharply separates an invariant to construct from its checked mathematical sufficiency.

## Lemma 1 — cross-ambient old socle coverage from one-sided upper-L inclusion

Let A and B be two independently chosen finite `EnumeratedPartialStructure db du dd` models. Fix the SAME source-coordinate cut `c`, with `c<A.size` and `c<B.size`. Let `originalA : Fin MA → Fin A.size`, `originalB : Fin MB → Fin B.size` be unrelated finite name maps, and `SelectedA`, `SelectedB` be arbitrary predicates. Write
`F=selectedStagePoolPrescribedData A c originalA SelectedA`,
`G=selectedStagePoolPrescribedData B c originalB SelectedB`.

Assume the full lower old L-socles are aligned:
```
SameInitialL A.L B.L c.
```
Assume *one-sided* inclusion of the COMPLETE allowed next-cut ordinary-L types:
```
∀ R : RelationalPrefixType (c+1) db du dd,
  F.PrescribedUpperLType R → G.PrescribedUpperLType R.
```

Then for **each** `S∈F.source` there is `T∈G.source` with
```
SameInitialL (prescribedOrdinarySocle (F.target S))
             (prescribedOrdinarySocle (G.target T)) c.
```

Proof: take `R=(F.target S).lReduct`, which is allowed by F. Upper-type inclusion supplies a **real source** `T∈G.source` with R equal to the complete reduct of its chosen G.target. Use the already checked actual original-representative theorem `selectedStagePoolPrescribedData_source_original` on each side. Each *chosen* target is the actual `A.partialTypeAt (c+1)` or `B.partialTypeAt(c+1)` of some eligible selected original, so the checked `ambient_partialType_prescribedSocle` identifies its prescribed old socle with its own ambient old ordinary-L segment. Compose this equality with `SameInitialL A.L B.L c` and reverse the B-side equality in **all four fields**, namely carrier membership, ordered binary, unary and diagonal atoms. No name-label isomorphism, nonemptiness hypothesis, or E comparison is needed. In particular, if F is nonempty then the upper inclusion itself forces G to be nonempty, avoiding the previously troublesome empty-profile case.

## Lemma 2 — one-sided complete B3 transfer across two ambients

Under Lemma 1's hypotheses, if `G.CorrectedB3 family` then `F.CorrectedB3 family`, by the existing verified `correctedB3_of_Lprofile_dominance`. The source coverage is **derived**, not assumed. The conclusion concerns only finite L-only B3 continuation witnesses; E remains in source selection.

## Lemma 3 — complete cross-ambient B3 equivalence, including empty pools

If additionally `∀ R, F.PrescribedUpperLType R ↔ G.PrescribedUpperLType R`, then apply Lemma 2 in both directions. The reverse direction uses the reverse of the original `SameInitialL A.L B.L c`. Therefore:
```
F.CorrectedB3 family ↔ G.CorrectedB3 family.
```
Unlike the old single-ambient comparison, **neither source needs an explicitly chosen anchor** and the empty case follows automatically from the upper-L equivalence.

## Theorem 4 — full Henson B3 is a cross-occurrence cut-star invariant

Let `A1=finiteNumericH(normalizedGraphModel E1,k1,N1)` and `A2=finiteNumericH(normalizedGraphModel E2,k2,N2)` be genuinely **different** finite numerical-Henson instances, with independent names `original1:Fin M1→Fin N1`, `original2:Fin M2→Fin N2`, full closure sets `Z1,Z2`, selections `Full1,Full2`, actual normalized-family avoidance, complete graph symmetry, no loops and K_ell-freeness. Assume `ell≥2` and `ell≤ki+1` for both i, a common source-coordinate cut `c<min(N1,N2)`, that every selected name represents an actual closure crossing in its OWN ambient, and that each full Z has no (I2) competing meet at c.

Let
```
Star1(v) := Full1(v) ∧ A1.L.binary c (original1 v) = true
Star2(w) := Full2(w) ∧ A2.L.binary c (original2 w) = true.
```

Assume `SameInitialL A1.L A2.L c` and equality of the complete permitted next-cut ordinary-L types of these cut-star *selectedStagePoolPrescribedData* profiles:
```
∀ R, (StarProfile1.PrescribedUpperLType R ↔
      StarProfile2.PrescribedUpperLType R).
```

Apply Track D's verified *anchor-free* `henson_fullB3_iff_cut_star_of_no_i2` in each separate ambient, then Lemma 3 between the two Star profiles, then reverse the second normalization. Conclude
```
FullProfile1.CorrectedB3 (hensonForbiddenFamily ell hell)
  ↔
FullProfile2.CorrectedB3 (hensonForbiddenFamily ell hell).
```

This is the first **inter-ambient full corrected-(B3)** bridge in Track B. It genuinely permits independent parameter closures, physical E columns, name universes and selected originals. It does NOT compare full dependent L+ source orbits, nor identify two different cut coordinates.

## Theorem 5 — any inter-ambient B3 disagreement exposes a missing physical cut-star type

Retain all the actual assumptions above **except equality of the cut-star upper spectra**. Suppose FullProfile1 fails corrected B3, while FullProfile2 passes.

Then StarProfile1 fails by anchor-free normal form; StarProfile2 passes by its normal form. If every complete upper L reduct permitted by StarProfile1 were also permitted by StarProfile2, Lemma 2 (using the common old socle) would imply StarProfile1 passes, contradiction. Thus there is an upper type U permitted by StarProfile1 but not by StarProfile2. Unpack `StarProfile1.PrescribedUpperLType U`, and use the exact chosen-source representative theorem to find a **real physical original v** in Star1, cut-eligible, with the chosen complete next-level ordinary-L reduct equal to U. Consequently:
```
∃ v : Fin M1,
  Full1(v) ∧ A1.L.binary c (original1 v) = true ∧
  c+1 ≤ A1.freeLevel(original1 v) ∧
  ¬ StarProfile2.PrescribedUpperLType
      ((A1.partialTypeAt (c+1) (original1 v)).lReduct).
```
The missing type is therefore located at a **physical cut-neighbour in the failing occurrence**, not an arbitrary missing abstract support vector. In the K4 first-gadget example, the actual q2 auxiliary name is exactly the kind of datum that cannot be discarded from the full cut-star.

## Hostile checks before implementing

1. **Same source coordinate:** `c` is common to both A and B. Different target numerical cut ranks must first be transported to a shared Kpt source coordinate; no such map is silently supplied.
2. **Common old L-socle:** `SameInitialL A.L B.L c` is strong and is a genuine cross-occurrence obligation. Merely having the same selected graph-age F does not imply it.
3. **Full complete next L-reduct:** the cut-star profile is a set of `RelationalPrefixType (c+1) db du dd`, preserving all directed positive/negative L atoms, singleton data and the cut-edge.
4. **No E on age-test W:** independent ambient E data are allowed because corrected B3's witnesses carry L only. Their role in determining actual full closure source names remains.
5. **No (I2), both sides:** needed to normalize full B3 to the cut-star separately; the lemma comparing two arbitrary selected pools does not require this.
6. **Represented full names, both sides:** essential for applying the anchor-free Track D normal form; finite membership or cut eligibility alone is insufficient.
7. **Empty stars handled:** Lemma 1 makes nonemptiness of G follow from source+upper-type inclusion; Lemma 3 also holds when both spectra empty.
8. **No global selected-shadow inference:** Star includes *all* genuine closure-selected auxiliaries with a positive physical L-edge to c; cannot be replaced by selected active macrodiary branches.
9. **No mixed ambient original edge assumption:** U only encodes old-to-upper edges within each ambient. Upper–upper edges of arbitrary forbidden clique continuations remain freely chosen.
10. **Source targets chosen consistently:** chosen target `F.target S` must be recovered by `selectedStagePoolPrescribedData_source_original`, not by an arbitrary original sharing S.
11. **Failure direction:** if occurrence 1 fails and 2 passes, its missing upper type is required to lie in Star1 but not Star2. The reverse conclusion does not follow without swapping which occurrence fails.
12. **No occurrence-independent orbit:** B3 agreement is weaker than all I1/I2/I3 event records and labelled source/parameter target spans; Track E remains separate.
13. **No arbitrary cut reindexing:** equality of complete L reducts at two different cut lengths is not even type-correct; a transport/reindexing lemma is a future mathematical prerequisite.
14. **No infinite resolution:** both A1 and A2 are finite numerical-H structures, with full physical K_ell assumptions; no countable resolved diary embedding or exact BRD unavoidability follows.
15. **No artificial nonempty anchor:** the entire construction uses the anchor-free normal form verified by merged PR #122 and centrally registered by #125.
16. **No black-text modification:** do not promote the manuscript's global B3/upper/lower claims; mark only these exact conditional cross-occurrence criteria after hosted full CI.
17. **No vacuous abstract theorem:** the Henson application requires physical graph avoidance, real full-source representation and the complete cut-star of the **actual** closure—not a postulated equality of the full corrected-B3 tests.

## Verification gate

English proof/audit committed first. Proposed five new named endpoints in `Kk/B3CrossAmbientCutStar.lean`, centrally imported/axiom-registered. Latest merged main `498b83ec77871b5efd9c38c7a75491cbc261f6c9` has a successful full **535** standard-only report gate, run [43481519534](https://github.com/janhubicka/lean-kk/actions/runs/43481519534). The new exact-head full `lake build`, parser self-test, and **540** named strict standard-only transitive-axiom reports are necessary before merging. No verification claim before the gate succeeds.
