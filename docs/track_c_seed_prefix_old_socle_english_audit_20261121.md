# Track C — old seed prefixes automatically discharge complete OLD Kpt socle tests below their level

21 November 2026. English-first adversarial proof, BEFORE Lean. This is a source-geometric simplification of E79's maximal full OLD-prefix certificate, not a new unconditional diary theorem.

## Exact statement

Fix the actual normalized Kpt successor tree for a forbidden family `family`, ANY genuine old AlgorithmRun Rold on a seed set X at finite oldTop, and ANY genuine physical original O_v in a true finite numerical-H+ structure. Let x∈X be a full admissible Kpt node satisfying x≤O_v in the literal Kpt tree (ALL dependent ordinary L and directed auxiliary E coordinates included), and suppose the tested source cut c satisfies c<lev(x).

Then **without any old source-index enumeration, no new run, no zero-L assumption and no E-free endpoint assumption** the full OLD Kpt c-socle of O_v is covered in the actual pre-cut old closure:

`KptActualOldSocleCoveredAt family X oldTop Rold O_v c`.

The OLD witness is exactly the literal seed x. It lies in every pre-cut closure `closure_(Rold.I(c+1))(X)` by inclusion of seed sets, even if c is not selected. Since x≤O_v and c<lev x, the LevelTree ancestor of x at c equals the ancestor of O_v at c. In particular, this is **complete old Kpt ancestor equality**, not merely equality of selected graph-age or of positive L-bits.

Equivalently define `KptOriginalOldSeedPrefixAt` asserting existence of such x. Whenever this certificate holds at c, E79's full old-socle coverage holds automatically. As a corollary, for any set S_v of eligible candidate-crossing cuts of original v, if one seed x≤O_v has level strictly above the **MAXIMAL** S_v cut, the E79 maximal OLD-prefix certificate for v is discharged with NO separately chosen old witness.

## English proof

Let A=finiteNumericH(L,k,M), O=A.kptOriginal(v). Assume x∈X, x≤O and c<lev x. Since the literal Kpt LevelTree order is level-compatible, c<lev x≤lev O, so the c-ancestors of both nodes are defined. The normal LevelTree lemma says if y≤z and c≤lev y, then ancestor_c(y)=ancestor_c(z). Apply it to x≤O. The witness x lies in closure_(Rold.I(c+1))(X) because arbitrary seed sets lie in their closure for any selected-level set. Taking this x, the two crossing inequalities and literal ancestor equality proves `KptActualOldSocleCoveredAt`. No interface assumptions about finite index, source masks, graph age or monoid map are used.

For a finite eligible set S_v and its maximum m, if x≤O and m<lev x then substitute c=m. The above gives the exact OLD socle coverage E79 needs at maximal cut. Under E79's proven downward monotonicity, the SAME seed x also covers all lower cuts of S_v. The argument is valid for possibly disconnected S_v.

## Hostile audit

1. The comparison is x≤O_v in the **FULL normalized Kpt tree**. Ordinary graph-age shadow agreement or equality of selected L-neighborhoods alone does not imply it. Directed E and all negative ordinary L bits are retained.
2. The seed x must be in the ACTUAL old seed set X. A node only present in a proposed final pool is not automatically live at the tested pre-cut c.
3. The strict inequality c<lev x is essential. If c=lev x, x is a terminal, not a crossing witness; E79's old socle predicate requires crossing.
4. The complete original O_v need NOT itself belong to the old closure; only its prefix x does, which is why this avoids unnecessarily demanding full original membership.
5. This establishes OLD-prefix coverage, not equality of upper c+1 Kpt ancestors; the later upgrade to full old/upper crossing still requires physical zero-L/other genuine source geometry.
6. No new root or new AlgorithmRun is assumed; the current old seed x can be a legitimate dependent Kpt node, not necessarily a literal physical original.
7. The old Rold is a genuine AlgorithmRun in the formal statement for compatibility with E79, although the proof of prefix coverage only uses seed-in-closure and would work for any selected-level set.
8. The shortcut applies at ANY cut c with c<lev x, including odd/real/fake cuts. At an odd cut ending another E-parameter, it does not eliminate that terminal or prove quietness.
9. Existence of a high old seed prefix does NOT follow merely because the original is listed in the new physical source cover W; an original coordinate in W might have no old seed prefix high enough. Do not infer global success of all per-original tests from pool membership.
10. At a maximal eligible cut m with m≥lev x, this particular seed does not discharge the certificate. Another seed or an old generated closure node may be needed.
11. A finite physical original may have multiple valid old seed prefixes, which can be used at different cuts; the theorem is existential and does not choose a canonical one.
12. This is a source-geometric reduction of the remaining hypotheses. It does not bound the number of physical originals lacking high old seed prefixes independently of carrier size M.
13. The old source need not be boring; the ordinary E79 old socle coverage predicate makes sense at any cut. In later safe-cut application the old-boring condition remains independent.
14. No reverse old/new coherent finite index or common labelled inverse successor-monoid orbit follows from a literal prefix match for one original.
15. The source new Y and stage zero/free-end hypotheses used in C452 are not changed: the lemma only supplies one subcase of its maximal-prefix certificates.
16. At actual K4 q2/I2/E cuts the full Kpt comparison still matters; matching a low prefix does not delete genuine selected events.
17. Do not insert a new global GREEN BRD validation mark. Keep frozen black manuscript prose unchanged.
18. Run exact-head full Lake and strict qualified named transitive-axiom audits before merging the new theorem.

## Lean plan

- Module `Kk/TrackCSeedPrefixOldSocle.lean`, imports merged `Kk.TrackEOldSocleOriginalMaxFrontier` and Mathlib tactics.
- Define a literal `KptOriginalOldSeedPrefixAt` predicate with `∃x∈X, x≤O_v ∧ cut<lev x`.
- Prove general `kpt_actual_original_old_socle_covered_of_seed_prefix` from `SMTree.Envelope.subset_closure` and `LevelTree.eq_ancestor_of_le` (check orientation carefully).
- Specialize at max(S_v) to certify E79 maximal OLD-prefix obligation automatically when a seed lies above the max.
- Optional sharpened sufficient criterion for per-original max checks: if `seed prefix above max` or `explicit old-prefix witness`, the E79 maximal condition follows, by exact case split. No claim of global diary application.
- Register fully qualified #print axioms and full Kk import; require all standard-only strict reports and full project CI.
