# Track E E75 — bare-original Kpt seeds automatically avoid positive even-real I1 levels

**19 November 2026. English mathematical proof and adversarial audit committed BEFORE Lean.**

## Why this matters for E73

Track E E73 combines the verified full zero-L dependent crossing transfer (E72) and Track D's verified full structural no-I1 theorem at positive even-real numerical-H+ cuts. One remaining hypothesis is that no *initial NEW seed* ends exactly at the tested even-real cut. This is essential for arbitrary seed sets: adding all ancestors of a new root as initial seeds is known to create spurious (I1) events at many lower levels.

For a **BARE original-only seed family**, however, this hypothesis is a theorem of actual numerical-H+ free-level geometry, and does not need to be imposed independently. The main result below identifies exactly the valid domain.

## Theorem E75.1 — no bare physical original ends at a positive real even H+ coordinate

Let A=finiteNumericH(K,k,N) be one genuine finite numerical-H+ structure. For any original v∈Fin N, its normalized Kpt original type

    O_v = A.kptOriginal family hAvoid v

has actual Kpt height `LevelTree.lev O_v = A.freeLevel(v)`. By the already verified successor-tree lemma `finiteNumericH_positive_freeLevel_ne_realPosition`, any strictly positive free level of a genuine numerical-H+ original differs from EVERY real H+ coordinate `hPosition(k,idx,g)`, which is even.

Therefore if c=hPosition(k,idx,g)>0,

    for every v∈Fin N,  LevelTree.lev O_v ≠ c.

Proof: if equality held, A.freeLevel(v)=c>0, so the positive-free-level non-real-position theorem contradicts it.

The original may have free level zero; positivity of c excludes that case too. No symmetry of ordinary L, no family avoidance beyond construction of the original Kpt type, no AlgorithmRun and no graph clique assumptions enter the argument.

## Theorem E75.2 — all BARE represented seed sets have no such I1 seed

Let Y be any set of normalized Kpt seed nodes with the following exact property:

    ∀ y∈Y, ∃ v∈Fin N, y = O_v.

This is a set of ACTUAL **full original** Kpt source nodes. It is deliberately much stronger than the normal stage representation condition `Y⊆ambientPrefixPool`, which allows arbitrary initial segments of originals.

Then at every positive real H+ cut c,

    NOT ∃ y∈Y, LevelTree.lev y = c.

Proof: choose the corresponding original v and invoke E75.1.

An especially useful corollary concerns one bare-root stage:

    Y = X ∪ {O_new}

where every x∈X is itself a genuine original Kpt type and `O_new` is the actual new original. This Y satisfies the premise by a trivial union split. Thus a whole sequence of bare-original-only root enlargements retains the automatic even-real no-seed property.

## Boundaries

The lemma is **not** true for arbitrary sets of prefixes of originals: even-real ancestors of a taller original exist in its LevelTree chain. If one of these ancestors is inserted into Y AS A SEED, it has height exactly the even-real cut and causes a genuine new I1 event. E75 makes no claim about **generated** meet/parameter closure nodes: Track D's no-full-I1 theorem is separately required to exclude those at zero ordinary-L stage cuts.

Consequently E75 removes precisely the *initial seed-level* premise in E73 for real bare-original source constructions, not the full no-I1 condition by itself. The zero ordinary-L stage and OLD COMPLETE Kpt socle matching hypotheses remain substantial and unproved for the global resolved-Q diary. Odd/fake E/q2 microcuts (including numerical K4 cuts 10/22) are not erased.

## Adversarial checks (18)

1. The seed must be the complete actual Kpt original O_v, not an arbitrary old-level prefix O_v↾c.
2. The physical structure is an actual finiteNumericH(K,k,N), not a schematic graph with arbitrary free levels.
3. `v:Fin N` supplies the original carrier bound v<N.
4. `kptOriginal` has Kpt height exactly the canonical E-free level; no guessed generation height.
5. The tested cut c is a **real** numerical H+ address hPosition(k,idx,g).
6. Require c>0: zero free levels can occur and root cut 0 is not excluded.
7. Every positive numerical-H+ free level is odd; all real hPosition coordinates are even.
8. The verified strengthened theorem explicitly excludes positive freeLevel equality to real hPosition.
9. No odd/fake numerical source cuts are ruled out.
10. No symmetry of auxiliary directed E is assumed or inferred.
11. Ordinary-L symmetry is not needed for the seed-level lemma.
12. This is source geometry independent of any actual AlgorithmRun, its I and F or selection.
13. No statement that **generated** closure meets/parameters are absent at c.
14. No assumption that the original O_v itself must be positive-free; free=0 is allowed.
15. The set condition must quantify every seed in Y, including old and newly added ones.
16. One-stage union X∪{new} retains the premise only if all X are literal originals.
17. Prefix-pool representation is insufficient, and replacing it by literal original membership would be an invalid hidden assumption for an arbitrary earlier construction.
18. No unbounded diary, full relative B3, uniform source bound, common labelled source orbit or BRD number is proved.

## Lean acceptance

Prove E75.1 physical original free-level separation, E75.2 arbitrary set of literal originals separation, and E75.3 one-bare-original union corollary. Dedicated exact-head direct `lake build`, three qualified standard-only `#print axioms` reports with negative parser self-test, and independent full repository CI before merging. No frozen black mathematics altered; no premature BLUE manuscript marker. E73 can later consume this theorem to simplify its **bare-original** specialization.
