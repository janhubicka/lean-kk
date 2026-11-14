# Track C — unconditional I1/I2 structural event classifier from actual complete Kpt source

**14 November 2026; English-first proof and adversarial audit before Lean.**
Stacked on [PR #131](https://github.com/janhubicka/lean-kk/pull/131) and its prerequisite [PR #128](https://github.com/janhubicka/lean-kk/pull/128). These source modules preserve actual dependent full L+ types, not a marked-selected ordinary-L projection.

## C24: I1-or-I2 iff I1 or physical nonfunctionality (NO no-I1 hypothesis)

For a genuine Kpt closure Z and source cut p, write:
- `I1(Z,p) := ∃ z∈Z, lev z=p`;
- `I2Meet(Z,p) := ∃ a,b∈Z, SameComponent(a,b) ∧ lev(meet(a,b))=p`;
- `PhysicalFork(Z,p)`: there exist complete old T and two *different* complete upper U,V with both (T,U),(T,V) in the canonical `FullPhysicalClosureCrossing family Z p`.

**Exact theorem:**
```
   I1(Z,p) ∨ I2Meet(Z,p)
       ↔ I1(Z,p) ∨ PhysicalFork(Z,p).
```
No I1 exclusion is needed here: the I1 disjunct catches cut-level nodes, including trivial self-meets.

**Proof.** If I1 is true, both sides hold directly. Otherwise an I2 meet implies, by the already verified Track C no-I1 classification, a fork in the **complete raw Kpt old/upper types**. The new physical bridge in PR #131 turns that fork into an actual `FullPhysicalClosureCrossing` nonfunctionality witness. Conversely any physical nonfunctionality gives a genuine I2 meet by Track E's independently checked theorem; a physical node at level p gives I1. Crucially, do not claim that I2 implies nonfunctionality *without* considering I1: the condition is on the UNION of the structural event kinds.

## C25: exact finite active-index structural-event certificate in an actual numerical H+ AlgorithmRun

Fix finite H+=`finiteNumericH K k N`, a genuine AlgorithmRun R on real Kpt seeds X, and the complete one-run final closure `params` and actual Boolean mask `presentAt` from Track C.

At cut p<runHeight let `Zp=closure (admissibleKptSTree family) (R.I(p+1)) X`.

**Claim:**
```
I1(Zp,p) ∨ I2Meet(Zp,p)
  ↔
  (∃ i:Fin params.card, presentAt p i=true
                     ∧ lev(node i)=p)
    ∨
  (∃ i j:Fin params.card, presentAt p i=presentAt p j=true,
                         p<lev(node i), p<lev(node j),
                         oldAt(p,i)=oldAt(p,j),
                         upperAt(p,i)≠upperAt(p,j)).
```

This is an EXACT, finite, physical structural classification for the current run. The right-hand alternatives are computably expressible Boolean/finite-index tests once actual complete Kpt nodes are supplied; we do **not** claim an executable decision procedure for arbitrary classically constructed ambient type equalities.

**Proof.** For the I1 case, use the run-tail monotonicity `R.I(p+1)⊆R.I0` and the exact final-closure index to recover the unique active name. For the I2 case, use the Track C `I2Meet→I1∨fullFork` result and its reverse `fullFork→I2Meet`. The true finite-mask lemma translates full forks into active index pairs. Combine the two disjunctions. There is NO no-I1 assumption anywhere in C25.

## Consequence for subsequent I3 classification

If the entire right side is FALSE, then there is no I1 source node and no competing I2 meet. This is precisely the structural exclusion required by the checked successor-tree `algorithmI3_implies_nonSkippableClosureCrossing` / `algorithmI3_failsCorrectedB3` interface, once actual AlgorithmRun interestingness and the relevant source/target graph are identified. The theorem does NOT prove that the cut is interesting or that corrected B3 fails; those remain separate facts for D.

## Hostile checks

1. An I1 node z at cut p may witness the raw competing-meet condition via (z,z) but cannot cross p, hence no physical fork. Keep the I1 disjunct explicit.
2. Do not replace `R.I(p+1)` by final `R.I0`: an inactive closure node can introduce false event witnesses.
3. Only full Kpt raw L+ records are compared, including auxiliary E and zero atoms.
4. Both indexed fork witnesses must cross p; mere active status is insufficient.
5. The finite index is over actual closure nodes, not all `Fin N` originals and not unique meet recipes.
6. Distinct upper types over the same old type are required; multiple identical outputs are not I2.
7. SameComponent is required for the exact meet, and no artificial meet is taken across disjoint roots.
8. No-(I1) is used *inside the proof's case split*, not imposed on the final theorem.
9. A structural I1/I2 classifier alone does not classify I3 or corrected-(B3) events.
10. K4 auxiliary microlevels 10/22 remain actual candidates; selected-front ages do not detect all events.
11. The finite within-run index is not a common index between two distinct diary occurrences.
12. No arbitrary finite L-age witness gets a new auxiliary E expansion.
13. Physical realization of the canonical recursively resolved multi-root diary remains unproved.
14. No uniform bound on event-index size, common labelled monoid orbit or exact BRD degree is asserted.

## Acceptance

Lean module `Kk/NumericHStructuralCutClassifier.lean`, imported from PR #131. Three named theorem endpoints maximum, exact-head direct build, strict standard-only axiom audit. Leave central `Kk.lean`, manuscript and validation markers for Track G integration.
