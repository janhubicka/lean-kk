# Track E E89 — compress a finite seed family's physical root-original pool before counting maximal OLD-Kpt-prefix obligations

**22 November 2026. English proof and adversarial audit, committed BEFORE Lean implementation.**

## Motivation: the remaining |U| term

Verified E86 and the newer E87 source-suffix reduction bound the number of distinct original max-prefix witness tests for one genuine old Kpt AlgorithmRun by

    |Need| ≤ |U| + |actual selected OLD source levels|

(or the remaining old selected tail at later cuts). Unlike physical carrier N and scan-height gaps, the root-original pool U is still an external set of names, and could be artificially padded with originals unrelated to any initial seed.

The finite numerical-H+ source normal-form only needs U to REPRESENT the initial seed Kpt nodes. If the actual candidate new INITIAL seed family Y is FINITE and every y∈Y is below some actual original O_v whose name v belongs to U, then one can choose at most one representative v per seed y. Thus there is a smaller pool U'⊆U with

    |U'| ≤ |Y|
    Y ⊆ ambientPrefixPool(A,U').

This is a true physical source REPRESENTATION theorem, NOT a claim that the old given root pool U itself must have size ≤|Y|. The reduction changes the chosen stage-original pool, and therefore the E79 Need set; it establishes that a SMALL valid presentation is available for the subsequent upper-bound construction.

## E89.1 — finite represented seed root-pool compression

Fix ANY genuine enumerated partial structure A (in particular a true finite numerical-H+ structure), normalized forbidden Kpt family, avoidance witness hAvoid, finite original-name set U⊆Fin A.size, and a FINITE Kpt seed set Y represented by U:

    ∀y∈Y, ∃v∈U, y≤ A.kptOriginal(v).

Choose one such representative original `rep(y)` for each seed y∈Y, using finite classical choice. Put

    U' = {rep(y) : y∈Y}.

Then U'⊆U. Since images of finite sets cannot have larger cardinality, |U'|≤|Y|. Every y∈Y remains below its chosen original `rep(y)∈U'`, so `Y⊆ambientPrefixPool(A,U')`.

No AlgorithmRun, closure, successor theorem, or selected-level plan is required for this purely concrete representation theorem. The actual complete Kpt type relation (including dependent E and negative L) is preserved: y≤O_v is a literal Kpt ancestor relation, not graph-isomorphic type similarity.

## E89.2 — a small-root version of the E86 max-prefix test count

Specialize to an actual numerical-H+ `A=finiteNumericH(K,k,N)`, a TRUE old AlgorithmRun R on X of top h, and any FINITE represented candidate new INITIAL seed Finset Y. Choose U' from E89.1. Since E86 applies for ANY true physical root-original pool (its test support is defined relative to that pool), it follows that the E79 maximal-prefix ORIGINAL-name set for the representation U' obeys

    |Need(U')| ≤ |U'| + |SelectedOld(R)|
               ≤ |Y|  + |SelectedOld(R)|.

This bound is independent of the ambient carrier size N, boring numeric gaps, and padding in the originally supplied U.

It is only an EXISTENTIAL representation-dependent budget. The original `Need(U)` for an oversized U is not being bounded by |Y|, and the new U' changes which original representatives are included in the auxiliary source-stage accounting. The parameter-closed Kpt closure itself remains computed from the same seed nodes Y and old selected levels R.I(c+1); it is not altered by changing the bookkeeping root pool.

## Special caveat: one bare new original

The E77/E84 one-bare-root theorems assume not just Y⊆ambientPrefixPool(U) but the SPECIFIC new complete original name newV∈U. A completely arbitrary choice of U' from E89.1 need not retain newV if another original happens to represent the same Kpt node. To reuse the one-bare-root theorem without proving uniqueness of original representation, add newV explicitly:

    U'' = U' ∪ {newV}.

Then |U''|≤|Y|+1 and Y remains represented by U''. This gives a conservative one-step root bound; an optimized choice fixing `rep(O_new)=newV` may recover |Y|, but is NOT claimed without formally handling duplicate physical Kpt originals.

This is an important restriction for any attempt to turn E89 into a diary-uniform cardinal bound.

## Application and unresolved issues

If in the actual resolved diary construction the genuine initial seed set Y has cardinality bounded solely by the fixed diary (possibly after a verified canonical seed normalization), then E89 together with E86 yields a number of max-prefix test originals bounded by the diary seed count plus the ACTUAL old selected-level count.

But the selected-level count still needs a diary-uniform bound, and the full OLD-Kpt-prefix witnesses themselves must be built at their maxima. No common labelled inverse-source monoid orbit, cross-occurrence chronological normalization, unsafe E-free-end source-cut elimination, or sharp BRD follows.

The user-selected original root pool U may carry additional semantic role requirements (e.g. every root is a designated dummy of resolved Q). Choosing a smaller U' preserves representation of Y, but must NOT be asserted to preserve unrelated role/Plan hypotheses. Those must be separately shown to be inherited by subsets where appropriate.

## Hostile adversarial checks (22)

1. Y is explicitly a FINITE set (Finset) of ACTUAL Kpt seed nodes; not an arbitrary infinite source.
2. The input representation is literal `Y⊆ambientPrefixPool(A,U)`.
3. Prefix membership means there is a genuine physical original O_v with y≤O_v, including dependent E data.
4. The selected representative rep(y) is an ACTUAL address in U, not a fabricated graph-age code.
5. One representative per seed suffices; several seeds may share a representative, so |U'| can be smaller than |Y|.
6. The choice uses classical finite selection, not a new source closure or target AlgorithmRun.
7. The image U'⊆U by the chosen witness property.
8. The cardinal bound |U'|≤|Y| is finite-set cardinality, not a bound on Y's source-level span.
9. Every y remains represented by its chosen U' original, with the SAME concrete Kpt ancestor relation.
10. The theorem works for ANY enumerated partial structure A satisfying avoidance, not only numerical H+.
11. Replacing U by U' does not alter the actual seed nodes Y or `closure_I(Y)`; it changes only the bookkeeping original-stage pool.
12. E86's Need set MUST be recomputed for U'; it is unsound to claim that the previous Need(U) automatically has size ≤|Y|+selected.
13. E86 itself does not require an already constructed target AlgorithmRun on Y.
14. E86 counts distinct maximal ORIGINAL-prefix tests, not failure cuts/intervals.
15. A literal new bare original O_new may have multiple physical representatives if the Kpt original map is not known injective; no uniqueness is assumed.
16. E84 requires the named newV∈U, which a naive compressed U' might lose; include newV explicitly if reusing the one-root source theorem.
17. The conservative bare-root pool bound becomes |Y|+1 unless a chosen-representative normalization is verified.
18. A chronological/role Plan property of all U originals is preserved under taking subsets, but a property requiring U contain every designated Q block original need NOT be preserved.
19. |Y| may still depend on the finite realization; no uniform diary bound is asserted without a separate bound on literal seed count.
20. |SelectedOld| is a genuine old AlgorithmRun selected-level count, not guessed diary interesting levels; its diary-uniform bound is not proved.
21. K4 E/q2 auxiliary physical source cuts 10 and 22 remain possible and must be accounted for.
22. No common labelled inverse-source orbit or sharp BRD characterization follows just from root compression.

## Formalization gate

Build a standalone E89 module importing the physical ambientPrefixPool definition and merged E86. First prove the general finite Y Finset root-representative compression as existence of U'⊆U with cardinal ≤Y.card and actual prefix-pool containment. Then specialize to finite numerical-H+ plus one old genuine AlgorithmRun and use E86 to derive an existential original-max-prefix-test cardinal budget ≤Y.card+oldSelected.card for the chosen U'. Finally, optionally prove a one-bare-root conservative U'' containing newV and cardinal ≤Y.card+1. Use source-exact named `#print axioms`, a dedicated standalone Lake build with strict parser negative self-test, and independent full project CI. Do not edit frozen black manuscript prose, reactivate removed TODOs or promote a global diary-uniform result.
