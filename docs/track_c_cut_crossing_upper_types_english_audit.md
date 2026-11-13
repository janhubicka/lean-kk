# Track C second stage: full parameter-closed crossing graph and physical upper types

**13 November 2026 — English mathematical proof and adversarial audit, BEFORE Lean.**

Scope: finite exact numerical `H^+` at **one actual Algorithm 5.4 cut**, with the complete
Kpt meet-and-selected-parameter closure. This strengthens
`docs/track_c_full_source_english_audit.md`. No claim about global resolved-copy
existence, equal source records across occurrences, or unconditional corrected (B3).

## C4. An eligible full-source H+ upper representative is REAL, not an odd fake target

Let `A = finiteNumericH K k N`. If an actual numerical vertex `v<N` has
`0 < A.freeLevel v`, then there exist *actual* indices `i,q` with `q<=k` and
`v=hPosition k i q`.

**Proof.** By the canonical free-cut equivalence, `A.E 0 v=true`.
The exact finite-E definition then implies `exactHEBool k 0 v=true`.
Unpack the literal generator: its target is necessarily
`hPosition k i q` for some `q<=k`. This uses the physical E
generator directly, not an evenness-to-encoding arithmetic surrogate.
A fake odd target is impossible, since each H-real target is even.

This is stronger than saying every odd fake coordinate has zero
incoming L atoms: odd coordinates may be **positive incoming E
predecessors** of a real upper target, but cannot themselves be a
positive-free-cut *target* of an E column.

## C5. The complete parameter-closed cut source, not a selected shadow

Fix the actual finite numerical partial structure
`A=finiteNumericH K k N` and a normalized family avoiding `A.L`.
Let `X` be the concrete Kpt seed set, and `U ⊆ Fin N` an original-name
pool with the *actual* prefix representation
`X ⊆ ambientPrefixPool family A hAvoid U`.
At an arbitrary level set `I`, let

`Z = Envelope.closure (admissibleKptSTree family) I X`.

By the already validated, **nontrivial parameter-closure invariant**,
`Z ⊆ ambientPrefixPool family A hAvoid (ambientStagePool A U I)`.
Thus every `z∈Z`, including nodes produced by repeated meets and
parameters, lies beneath the complete Kpt type of **one ambient finite
H+ vertex** `v:N`. This proof does not assume that z itself is an
original or that its level is a real coordinate.

Fix an index `p` and the genuine corrected-(I2) *no-competing-meet
at p* condition

`¬∃a,b∈Z, SameComponent(a,b) ∧ lev(meet(a,b))=p`.

Define `F` as the **closure-selected** prescribed source from these
exact numerical H+ names:

`F=closureSelectedBoringData family A hAvoid id Z p`.

Then THREE statements hold:

1. **Forward coverage (every actual closure crossing).** For every
   `z∈Z` with `p < lev z`, there exists `T∈F.source` such that
   `⟨p,T⟩` and `⟨p+1,F.target T⟩` are exactly the consecutive
   ancestor types of that same z. This is the full, corrected
   `CoversClosureCrossing` predicate, not an inclusion only on
   marked selected originals. The no-(I2) condition ensures
   that nodes with equal old types cannot disagree on next types.

2. **Reverse full source / upper-type witnesses.** Every
   `T∈F.source` has a same-vertex representative `v∈Fin N` with
   `p+1 ≤ A.freeLevel v`, `T=A.partialTypeAt p v`, and
   `F.target T=A.partialTypeAt (p+1) v`. Moreover C4 forces
   `v=hPosition k i q` with `q≤k`. The assigned upper type
   includes *all* L and auxiliary E data, including zero atoms and
   diagonal/unary bits where present; it is NOT just an ordinary
   selected-front adjacency profile.

**Proof.** Apply `admissibleKpt_stage_closure_subset_pool` to
discharge the entire closure representation from the honest seed pool
hypothesis. With `original : Fin N→Fin N := id`, the source
`F` is by definition the `closureSelectedBoringData` of that
full stage. Apply the checked
`closureSelectedBoringData_covers` using the stage representation
and the no-(I2) meet condition. Finally unpack
`selectedStagePoolPrescribedData_source_original`: every source type
comes from one selected and cut-eligible ambient name whose **full
next type** is *definitionally* the prescribed output. Since its free
cut is at least `p+1>0`, C4 identifies the witness as a genuine
numerical H real coordinate. No fake target is silently introduced.

The same statement applies at any cut `p` of an actual AlgorithmRun R
by taking `I=R.I (p+1)`; require `p<runHeight` and the no-(I2)
condition for the **same** pre-cut closure.

## Adversarial checks

1. **Do not confuse fake E predecessors and fake E targets.**
   Odd coordinates below a top free cut can be incoming E-positive
   while their own incoming E column is empty. C4 concerns *target*
   representatives with a positive free cut.
2. **Retain actual source membership.** The formal F uses
   `closureSelectedOriginal`, not all vertices with long free cuts,
   and certainly not only selected visible-front originals.
3. **No-(I2) is indispensable.** Duplicate old source types with
   different next types do not yield a well-defined F covering all
   actual crossings. The rejected configuration is exactly a meet
   at level p of two same-component closure nodes.
4. **Full meet-and-parameter closure.** Z is not the raw seed X
   or a selected shadow; the stage-pool invariant must include every
   actual selected positive parameter.
5. **Seed pool preservation remains an assumption.** For a
   recursively scheduled resolved copy one must establish the seed
   prefix pool at EACH stage. A standalone finite graph does not.
6. **Same H+ structure and family.** All `partialTypeAt`,
   `freeLevel`, `kptOriginal`, and forbidden-family avoidance
   refer to one fixed `finiteNumericH K k N` throughout.
7. **No arbitrary auxiliary E on age witnesses.** The source
   equality is between full types extracted from A itself; any
   corrected-(B3) age witness remains a separate ordinary-L model.
8. **The physical real witness can have generation zero.**
   C4 only proves `q≤k`; it does NOT claim `0<q`, which would
   be a false unproved gap. Positive free levels impose additional
   restrictions only when separately established.
9. **Prefix/upper level index.** The record is `p` and
   `p+1`, with `p+1≤A.freeLevel v`. Off-by-one weakening to
   `p≤freeLevel` loses the actual next type.
10. **K4 cuts 10 and 22.** Their genuine additional selected
    numerical microcuts must remain in Z and must not be ignored
    because a marked-selected shadow appears unchanged.
11. **No automatic B3 or orbit.** Full crossing coverage alone
    does not prove corrected B3, global boringness, a common labelled
    inverse source, or the BRD characterization.
12. **F is a chosen prescribed map.** The theorem identifies
    the canonical closure-selected F and shows it respects all
    actual crossings under no-(I2). It does not assert that an
    independently defined manuscript implementation of f_p equals
    this F until its own identification lemma is proved.

## Exports

- `finiteNumericH_positive_freeLevel_has_real_target` (C4).
- `finiteNumericH_full_cut_crossing_and_upper_types` (C5).
- `finiteNumericH_run_cut_crossing_and_upper_types` (AlgorithmRun form).

Require direct isolated `lake build Kk.NumericHFullClosureCrossing`,
exact `#print axioms` for all three exports, and final exact-head
full-project build. Keep manuscript source and validation marks frozen
for integration owner G.
