# Track C — genuine physical H+ live-source trichotomy (English first)

18 November 2026. Mathematical candidate, not yet kernel checked.

## Statement

Assume exactly the hypotheses of the merged physical constructor
`Kk.finiteNumericH_constructed_composable_coherent_source_index`:
two forbidden-free finite numerical-H+ structures, complete old original
binary/unary/diagonal prefix fidelity, old seeds physically represented,
positive root and chronological bounds, and an actual old exhaustive
Kpt AlgorithmRun.

The existing verified constructor produces true old/new AlgorithmRuns,
finite old/new *Finsets of full dependent Kpt nodes*, their canonical
Fin-index enumerations, per-cut Boolean live masks, and a coherent
injection e of horizon oldTop.

For every cut c<oldTop and every **new-live target index** j, precisely
one of the following three classes holds at the level of full Kpt nodes:

* **Transported old-live:** j=e(i), oldLive(c,i)=true.
* **Reactivated old-name:** j=e(i), oldLive(c,i)=false, so the literal full
  Kpt node was already present but its cut-live mask has changed.
* **Literally fresh:** no old indexed node equals the new full Kpt node.

The three classes are pairwise disjoint because the canonical target
Finset enumeration is injective and e is injective.

## Proof

Invoke the already verified physical constructor #304 to obtain
oldParams, newParams, e, oldLive, newLive and genuine runs.
Fix c and a new-live j. Decide whether an old *live* i maps to j.
If so we are in the first class. Otherwise use the exact cut-live
residual dichotomy, applied to the canonical injective enumeration
of newParams. This says either (a) j=e(i) for an old *inactive* i,
or (b) there is no old indexed full Kpt node equal to the new node
at j. These are exactly the second and third classes.

The disjointness of the first and second classes follows from
injectivity of e and incompatible oldLive Boolean bits.
The third class is disjoint from the first two by literal identity.
The theorem can be stated as an exhaustive disjunction without
needing an intricate mutually exclusive sum type in Lean.

## Hostile audit

1. The conclusion refers to full admissible Kpt node equality;
   **not** merely equality of old ordinary graph-age shadows.
2. It uses true canonical finite source Finsets; an arbitrary duplicate
   node enumeration is not sufficient.
3. The third case is relative to the *old complete finite source*.
   It is not a novel source relative to all other diary occurrences.
4. The second case is **not** new at final closure and may not be
   discarded by counting only fresh final parameter nodes.
5. The theorem proves *classification* of new-live indices but not an
   a priori bound on the size of the second and third classes.
6. No off-plan residual elimination follows automatically.
7. Genuine H+ forbidden-avoidance, exact old original columns and
   root chronology remain hypotheses exactly as in the constructor.
8. All auxiliary K4 q2 and I2/E data remain inside full Kpt nodes.
9. The source injection is not a reverse coherent map.
10. Complete old/upper L+/E records on transported names follow
    from literal identity; live masks are external and may differ.
11. The result is a finite-stage theorem, not an infinite Ramsey
    color homogeneity or common inverse monoid-orbit statement.
12. Do not add a GREEN manuscript mark until the new specialized
    theorem has its own exact-head successful build and axiom report.

## Planned Lean form

New module `Kk/PhysicalLiveSourceResidual.lean` imports the exact
physical coherent-index adapter and the generic cut-live dichotomy.
It repeats the physical constructor hypotheses literally and returns
canonical finite source indexes plus the three-way classification at
all cuts less than oldTop. No new existence assumptions on the new
AlgorithmRun or new index are allowed.

## Verification gate and manuscript intervention

The new source file is explicitly imported into `Kk.lean`, so an
ordinary complete `lake build` cannot silently omit the proof.
Its fully-qualified theorem name is also included in the central
`scripts/check_axioms.lean` transitive-axiom report. This is different
from the earlier green project build that had not imported Track C.

**Not yet certified:** the current branch has no reported exact-head
success at the time of this audit. In particular, the theorem is only
a proof candidate and should not receive a manuscript validation mark
or be merged before the strict build/axiom gate succeeds.

**Olive manuscript edit after certification:** describe the true
finite-stage *three-way source classification*, without claiming
elimination or uniform boundedness of the two residual classes.
**Frozen black text:** unchanged; its unsupported implications should
receive existing TODO annotations rather than editorial rewrites.
