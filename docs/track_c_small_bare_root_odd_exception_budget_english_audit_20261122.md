# Track C: the bare root needs only inherited originals plus ONE new original

22 November 2026. English mathematical proof and hostile checks, committed **before** the Lean source.

## Improvement over verified PRs #446 and #473

Fix two genuine numerical-H+ finite physical structures
(A=finiteNumericH(K,k,N)) and (B=finiteNumericH(L,k,M)),
with (N\le M) and the exact old-block agreement hypotheses on all
binary/unary/diagonal base atoms. Assume the full normalized forbidden
family is avoided by both, and a *finite* old root-original pool
(U\subseteq Fin\,N) covers every literal initial OLD dependent Kpt seed
(X): each seed is a full Kpt prefix of an (A)-original named in (U).
The bare new-root seeds in (B) are precisely
(Y=X\cup\{O_w\}), with the one TRUE physical new original
(w=hPosition(k,j,k)<M).

**Small bare root pool.** Define
[
  W=(Fin.castLE(N\le M))[U]\cup\{w\}\subseteq Fin\,M.
]
Then (|W|\le |U|+1) and (Y) is contained in the complete
dependent Kpt original-prefix pool represented by (W).

**Actual run / exception theorem.** Under the full physical chronological
hypotheses of the existing verified
`finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle`,
including a TRUE old AlgorithmRun `Rold` on (X), construct this
**smaller** concrete W, and let (F) be the image by the canonical
physical E-free-level map of the actual FINAL stage originals
`hStageOriginals L k M W (Rold.I 0)`.
Let (S_{old}={q\in Rold.I 0}), a finite set of ACTUALLY selected
old levels. Then
[
  |F|\le\min\bigl(M,\ |U|+|S_{old}|+1\bigr).
]

For EVERY old-unselected odd source cut (c=2a+1<oldTop)
outside this **specific** F, absence of a full stage-original E-free
end follows from the actual old run's selected tail. The chronological
new root has E-free end `newTop\ge oldTop>c`, so does not itself end
there. If the complete OLD Kpt prefix witnesses of all genuinely
active original representatives at this cut are supplied, the
existing verified physical odd theorem proves **full candidate
no-novelty**, including I1 and the SAME-node complete dependent
old/upper L+/E crossing relation.

The new bound depends on old roots and actually selected old levels,
but NOT the padded new carrier M or the lengths of old boring gaps,
except via the explicit min(M,-). It is still NOT a global BRD or a
diary-uniform bound until `|U|` and `|S_old|` are bounded by the
fixed abstract diary.

## Proof in English

1. Use the already kernel-verified
   `finiteNumericH_baseExtension_old_seedPool_lifts` with the genuine
   old (U) to obtain (X\subseteq PrefixPool_B(cast[U]));
   this transports **complete** old Kpt original nodes (all old
   L and directed auxiliary E atoms), not just their graph shadows.
2. The bare set (Y) is exactly (X\cup\{O_w\}). Enlarge
   the transported root set to (W=cast[U]\cup\{w\}).
   Its original-prefix pool covers old (X) by (1) and covers
   (O_w) reflexively. The image cardinal is no greater than
   (|U|), and adjoining one element increases cardinality by at
   most one. Thus (|W|\le |U|+1).
3. Take the genuine old physical AlgorithmRun from the hypothesis
   `HasPhysicalExhaustiveKptRun`. Put
   (F={B.freeLevel(v):v\in hStageOriginals(W,Rold.I0)}).
   Verified E86 / PR #473 give
   (|F|\le |W|+|S_old|), while independent PR #446 gives
   (|F|\le M). Substitute the new (|W|) bound and combine with
   `Nat.le_min`.
4. For any (c<oldTop) outside (F), verified
   `kpt_physical_no_stage_free_end_outside_final` excludes every
   stage-original endpoint at (c); the hypothesis that the old
   run is genuine is essential here.
5. If (c) is old-unselected, use
   `Rold.interesting_step` to show it is truly old-boring. The
   chronological old-top comparison follows from the old *actual*
   top seed and (N\le newTop). The new root has exact physical
   E-free-level (newTop), so its endpoint is not (c).
6. Apply the verified
   `finiteNumericH_old_boring_one_bare_odd_noNovelty_general`
   to exactly these (W,Rold,Y,c), retaining the explicit COMPLETE
   old-Kpt-prefix hypothesis. This gives full candidate
   `NewRootNoNoveltyAtCut`.

## Hostile audit before Lean

1. (U) is a **Finset of physical original names**, not an abstract
   graph vertex set or inferred finite support.
2. Actual old seed membership is in the original full dependent Kpt
   prefix pool. A selected ordinary-L type is insufficient.
3. The old-to-new prefix lift uses *all* old binary, unary and
   diagonal atoms and the fixed auxiliary-E physical encoding.
4. The old bases satisfy (N\le hPosition(k,b,0));
   otherwise base extension can alter old numeric records.
5. The new family avoidance hypotheses are not inferred from a
   graph-only free-amalgamation property.
6. The new bare seed set has **only one inserted physical original**,
   not its entire prefix chain or old closure-as-initial-seeds.
7. The chosen W is a root pool for Y only. Its selected-stage closure
   may contain other physical originals, as counted separately by
   actual selected levels.
8. W need not contain every selected-parameter address; the verified
   `ambientStagePool` mechanism adds these during source closure.
9. (w) can already lie in cast[U] formally. Use \(\le|U|+1\),
   not an unwarranted equality.
10. `Fin.castLE` is an injection, but bounding image cardinality
    only requires the general \(card(image)\le card(source)\).
11. The actual stage (hStageOriginals) may include additional
    **positive selected** originals outside W. Do NOT identify
    the final stage with W.
12. The selected level count includes the genuine old top level.
    Excluding it would produce a false bound.
13. Neither (F) nor its endpoint map is assumed injective.
14. (F) is the image of the complete FINAL stage from the SAME
    old run and W used in the no-novelty conclusion.
15. The finite cardinal bound concerns physical E-free endpoints,
    not every I2 meet, bad factor, K4 auxiliary event, or real
    nonzero ordinary-L cut.
16. An odd cut in (F) can be genuinely active; it is not deleted
    by this argument.
17. The new root cannot have E-free end below oldTop because its
    actual top is `hPosition(k,j-1,k)+1`; this uses `k>0,j>0`.
18. The oldTop≤newTop proof must use a REAL old-top seed from
    `HasPhysicalExhaustiveKptRun`; the artificial top marker
    alone is insufficient.
19. Complete OLD socle witnesses for each stage source remain
    explicit conditional inputs; they are not deduced merely
    from the small cardinality of W.
20. Same-node full dependent L+/E crossing matching follows only
    from the separate verified physical odd no-novelty lemma.
    Counting alone does not give it.
21. This result is independent of arbitrary reindexing of the
    larger (physically taller) new AlgorithmRun and does not
    identify inverse-source monoid orbits.
22. The result is at most a **diary-shaped** bound until abstract
    diary realization controls both |U| and |Rold.I0| uniformly.
23. Both the English statement and Lean declaration must retain
    the genuine complete K/L two-model physical extension. No
    weakened graph shadow may be silently substituted.
24. Exact-head source build, central qualified transitive-axiom
    gate and parser/self-test are mandatory before considering
    the Lean statement verified.

## Lean tasks

Implement
`finiteNumericH_bare_root_small_original_pool` in arbitrary
dependent signature `db du dd`, obtaining `W.card\le U.card+1`
and literal prefix-pool coverage of (Y). Then implement
`finiteNumericH_constructed_odd_quiet_outside_small_root_budget`
in graph signature (1,0,1), with one genuine chronological old run,
specific final F and full conditional no-novelty at odd safe cuts.
Register named `#check` and `#print axioms` in the central gate,
CI-check all tracks; do not touch frozen black manuscript text.

## After this lemma

Bound the inherited *old* root count and selected Kpt event count by
a fixed abstract diary. Derive complete raw old-seed matches from
actual resolved-Q geometry at maximal safe cuts, then deal with the
finitely many exceptional E cuts, nonzero real cuts and the taller
new-run labelled inverse-source orbit. No BRD assertion yet.
