# Track C: repaired root-ONLY seeds do not preinsert lower I1 nodes

**14 November 2026 — English proof and adversarial audit BEFORE Lean.**
Stacked on mathematically corrected PR #165 `finiteNumericH_physicalExtendedSeeds`: initial seeds are full inherited old Kpt closure UNION **actual new Kpt ORIGINAL nodes**, not their whole ambientPrefixPool. Compare with independently formalized overgeneration obstruction PR #183 (initial prefix saturation forces ALL AlgorithmRun levels I1).

## Corrected seed definition and objective

Let B=`finiteNumericH L k M`, let `family` be avoided by its actual L-reduct, X any old admissible Kpt seeds and I any selected-level set. Let W⊆Fin M be actual newly inserted physical original names. The new seed set is

```
Y = closure (admissibleKptSTree family) I X
      ∪ ((fun w : Fin M => B.kptOriginal family hAvoid w) '' W).
```

Let `oldZ = closure ... I X`.
Assume **every** newly seeded root has precisely the same true canonical E free cut t:
`∀w∈W, B.freeLevel(w)=t`.

### R1 — all new root seed nodes have exactly level t

For any z in the image of W under the *actual Kpt original* map, z is some `B.kptOriginal w`. The verified Kpt original LevelTree level is `B.freeLevel(w)=t`, so lev z=t. No arbitrary E was supplied; this is the literal generated physical L+ type.

### R2 — lower-level I1 in Y iff already present in inherited old closure

For any p<t,

```
(∃ z∈Y, lev z=p) ↔ (∃ z∈oldZ, lev z=p).
```

**Proof:** the reverse direction is immediate by the first union summand. For the forward direction, an alleged level-p node z∈Y either belongs to oldZ, which witnesses the right side, or belongs to the new-root image. In the second case R1 yields lev z=t, contradicting p<t. Hence every lower-level initial seed came from the inherited old closure.

This eliminates the *automatic* new-root prefix-saturation problem of the original PR #165, while retaining the entire old parameter-closed seed part.

### Precise boundary: do not confuse seed membership and actual pre-cut closure

The actual Algorithm 5.4 I1 predicate at cut p is evaluated on
`closure (admissibleKptSTree family) (R.I(p+1)) Y`,
NOT on Y alone. New-root **selected-parameter closure** can generate additional p-level nodes even when no initial p-level seed exists. Therefore **R2 does NOT assert the actual AlgorithmRun omits any lower level**, and does not prove the resolved diary height is uniformly bounded.

This is why the result is an exact source-construction regression, not a new global boring-level theorem.

## Hostile checks

1. The new summand must be an IMAGE of the genuine original Kpt node map, not an ambientPrefixPool of all its predecessors.
2. Y includes all inherited old closure nodes; lower I1 witnesses can still occur there.
3. Every new root's FREE level must be t for R1/R2; heterogeneous free levels can produce lower newly inserted I1 seeds.
4. Kpt original level is its true auxiliary E free cut, not the physical original numeric address.
5. All positive and negative L and auxiliary E bits live in the actual admissible Kpt original; no fake E is assigned to a separate age witness.
6. The proof covers arbitrary multiple real new roots W with equal E free cut, not just singleton root.
7. If W is empty, R2 reduces to a tautology; the theorem does not assert a top seed.
8. The assertion concerns SEEDS at level p, not pre-cut parameter closure in the actual AlgorithmRun.
9. Do not assert the repaired construction has no additional auxiliary I1/I2/I3 events; only automatic lower-level initial I1 is excluded.
10. This does not prove the source pool is uniformly small or a bounded resolved diary.
11. New Henson original columns still require a legitimate complete old/gap K_(ell−1)-free check.
12. The chronological old-carrier cutoff of stacked PR #185 is a separate condition for bounding all inherited old seeds.
13. The K4 real auxiliary cuts 10/22 remain possible and are not projected away.
14. No cross-occurrence source-orbit synchronization or unconditional BRD number is inferred.

## Lean acceptance

New `Kk/NumericHRootOnlyI1Regression.lean`, two exact named theorem endpoints and strict standard-only transitive axiom reports. Targeted exact-head direct module build and full-project CI. Track G owns `Kk.lean`, shared registry, manuscript and validation marks.
