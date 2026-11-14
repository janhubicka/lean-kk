# Track C — critical repair: do NOT seed all prefixes of each new root

**14 November 2026, English proof, counterexample and adversarial audit BEFORE the Lean edit.**

## A fatal overgeneration in the original PR #165

The original definition in `NumericHPhysicalNewRootRun.lean` was

```
Y_bad = closure (admissibleKptSTree family) I X
         ∪ ambientPrefixPool family B hAvoidB W.
```

For a new original w∈W with true Kpt free level t, the physical prefix pool contains **every** Kpt ancestor of the original o=B.kptOriginal(w) at levels p≤t. In particular, for each p<t there is y∈Y_bad with lev(y)=p.

Since any stage pre-cut closure contains the seed set Y_bad, Algorithm 5.4 condition (I1) fires at *every* p<t, regardless of the newly prescribed L adjacency column or any corrected-(B3) age test. Hence every genuine AlgorithmRun R on Y_bad with top=t selects **all** levels p=0,...,t (the top level is selected by definition). This is a mathematical obstruction: the construction is not a bounded resolved-diary construction. A kernel-clean finite index theorem about Y_bad is true but nearly useless for the intended bounded upper bound.

The problem comes from confusing two notions:

- `ambientPrefixPool B W` is the **covering ambient source set** of nodes under physical originals, used to witness the closure invariant.
- The *initial seed set* of the successor algorithm must remain small: it should include the chosen **new original types**, not all their ancestors as independent seeds.

Putting an entire prefix pool among the initial seeds is a serious overgeneration, not a harmless strengthening.

## Corrected geometric seed construction

Define

```
Y := closure (admissibleKptSTree family) I X
      ∪ ((fun w : Fin M => B.kptOriginal family hAvoidB w) '' W).
```

Here B=`finiteNumericH L k M`, and W⊆Fin M is the set of ACTUAL newly inserted physical originals.

The new seed set contains all inherited old meet/parameter-closure nodes, plus the **new actual original nodes themselves**. Their proper prefixes belong to the covering ambient prefix pool but are **NOT** inserted as extra seed nodes.

### C38' — source-pool invariant without an arbitrary hNext hypothesis

The verified old-source base-extension theorem transports X into a genuine prefix pool of B based on U'=`Fin.castLE '' U`. Every old closure node is therefore covered by `ambientStagePool B U' I`.

For every new z in the right-hand image, `z=B.kptOriginal w` for an actual w∈W; hence z belongs to `ambientPrefixPool B W`, with witness its own physical original and reflexivity of the Kpt prefix order. Thus the **corrected Y** is a subset of

```
ambientPrefixPool family B hAvoidB
  (ambientStagePool B U' I ∪ W).
```

This discharges the arbitrary `hNext` premise by the ACTUAL definition of Y, not by assuming that all prefixes are initial seeds.

### C39' — actual run and full final source index

Suppose there is w∈W with canonical E-free level t. Then its actual Kpt original lies in corrected Y and has level t. Invoke the verified `canonicalAlgorithmRun` theorem to construct a real run R on Y of height t. Its entire final meet/parameter closure is finite by the true numeric-H prefix-pool invariant, so Track C's existing exact finite source index and `presentAt` mask apply.

No claim of I1 at all levels follows from the new-root part: only the particular new node of level t was inserted, not its proper ancestors.

### C40' — top-generation real root

If k>0, j>0 and `w=hPosition k j k<M`, then the existing exact physical E column gives

`B.freeLevel(w)=hPosition k (j-1) k+1.`

Taking W={w} constructs the genuine top seed and full indexed AlgorithmRun at that E-free cut; no fake E is added.

### C40b' — bound the ENTIRE corrected new seed set

Under the additional chronological old-carrier bound

`N ≤ hPosition k (j-1) k+1`,

the old X has levels ≤N (because every old z is below the true Kpt original of some v<N, and fl(v)≤v). Verified closure-finiteness/level preservation gives `closure I X⊆levelLe(t)`.

Every new seed is exactly the one top Kpt original o of level t (not an arbitrary node); hence Y⊆levelLe(t). This is the actual bound needed for the successor-tree bounded-envelope theorem.

## Hostile checks and remaining obligations

1. The old definition forces all I1 levels; it is mathematically unsuitable even though its finite source theorem can be kernel-true.
2. `ambientPrefixPool` is a source **cover**, not a recommended set of **initial seeds**.
3. The corrected right summand contains only ORIGINAL types, not their entire prefix chains.
4. The verified meet/selected-parameter closure of corrected Y may still generate additional auxiliary nodes and I1/I2/I3 microevents; no unjustified elimination is claimed.
5. The inherited old closure is kept **entire** as seeds: this might itself overgenerate at some levels. Its exact minimality and compression must still be audited; the present fix eliminates only the *new-root* saturation.
6. The corrected Y is constructed, not a hypothetical set with a postulated coverage predicate.
7. New W represents actual physical `Fin M` originals and includes their exact complete directed L/E type.
8. Generated E free cuts, not numerical physical positions, determine Kpt node levels.
9. Exact K→L old-original preservation needs fixed k, N≤hPosition k b 0, old L-column agreement, and true forbidden avoidance on both physical models.
10. Existing actual-Kpt closure and next-stage pool proofs transport X across the physical base extension; nothing invents an E expansion of a separate L-only age witness.
11. The run is genuinely constructed from `normalizedKptSMTree`, not postulated, but finite construction alone does not bound envelope height independently of t.
12. For boundedness, the explicit old-carrier inequality N≤t is necessary; one top-level seed does not automatically bound others.
13. A new root with free level zero cannot supply a positive selected top; k>0 and j>0 are essential in the numerical top formula.
14. No cross-occurrence labelled inverse-source orbit is established.
15. Exact new-reserved Henson backward column, whole old/gap K-free certificate and chronological recursively safe schedule still belong to Tracks A/B.
16. The K4 actual auxiliary cuts 10/22 are not erased by this repair.
17. One complete finite indexed run is still not the bounded *canonical resolved diary* required for unconditional BRD numbers.

## CI and integration

Modify `Kk/NumericHPhysicalNewRootRun.lean` in the existing DRAFT PR #165, not the protected manuscript. Retain four theorem endpoints; their statements use the corrected **definition** of Y. Re-run the isolated exact source module check and FOUR named transitive axiom reports with only standard axioms, plus independent full-project Lean CI at the same head. Track G controls central imports and validation marks. The old proof wording/docstring must be corrected; it may no longer say 'all new-root prefixes are seeds'.
