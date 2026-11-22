# Track F — physical canonical survivor deletion and exact zero-code reindexing

22 November 2026. English proof and hostile audit before Lean. This applies the independently kernel-checked trackFCanonical_reindex_mono (integer-witness restriction and extension) to genuine finite Henson fronts, rather than copying its proof.

## Exact raw and canonical reindexing

Fix any genuine edge table E, ell>0, level H, a full labelled front u : Fin(d) → HensonOneType(ell,E), and any injective selection of survivors f : Fin(e) ↪ Fin(d).

For each actual nonempty admissible support U, the FULL actual old-neighbour pool of the selected front u∘f on U is literally the full front's old-neighbour pool on f[U]:

common_E,H(u∘f,U) = common_E,H(u,f[U]).

A point satisfies the positive-neighbour conditions for all i∈U exactly when it satisfies them for all j∈f[U]. The prefix [0,H) is identical. Hence raw clique capacities and bounds agree.

The complete physical raw function is support-monotone by the verified common-pool inclusion theorem (#395). Apply the existing full normalized integer-witness reindexing theorem trackFCanonical_reindex_mono (module TrackFSurvivorCanonical) to obtain:

Canonical_(u∘f)(U) = Canonical_u(trackFMapSupport f U).

This is equality on EVERY admissible support, including triples. No witness axiom, no raw=canonical claim. In particular f = Fin.succAboveEmb j deletes exactly coded sort j from a genuine front on Fin(d+1).

## Across the actual zero-code coordinate

Assume explicitly ell>0, as normalized finite witness construction and its canonical reindexing require a positive clique threshold (the intended K₄ case has ell=4). Let the full genuine pre-code front p indexed by Fin(d+1) have level c, where c is the actual target image of a coded source original. Let v_i, i∈Fin(d), be genuine synchronized surviving target types reaching at least c+1, and each having bit zero at c. Write f = Fin.succAboveEmb j.

Assume the true old-positive-neighbour sets match:

N(p_(f(i))) = N(restrictPrefix(v_i,c)).

This is the survivor equality obtained by genuine restriction in the physical pre-code construction (draft PR #470), after reindexing into the TARGET surviving order. Both sides have level c; finite-type extensionality gives equality of the actual one-types, negative bits included.

Physical canonical reindexing gives Canonical_p(f[U]) = Canonical_(restrict v to c)(U). The verified complete zero-cut survivor theorem (#447) then gives Canonical_(restrict v to c)(U) = Canonical_(restrict v to c+1)(U), for EVERY nonempty support U. The deleted code coordinate imposes no phantom extra witness restriction.

## Hostile audit

1. f must be injective: merging sorts changes clique multiplicities.
2. The raw pool identity uses all actual positive neighbours on the same real prefix, not a coding or selected shadow.
3. The actual support and image support are nonempty and size-bounded. No empty graph-age coordinate is invented.
4. Canonical reindexing is NOT automatic for arbitrary raw B: the verified lemma requires support monotonicity, which the actual pools satisfy.
5. Fin.succAboveEmb j preserves the survivor order at the ACTUAL TARGET cut, not necessarily source lexicographic order.
6. All surviving types must reach at least c+1 and have zero bit c, including third-sort survivors.
7. Pre and before-cut types are genuine consistent target one-types at EXACT level c. Equality of neighbour fields implies equality by proof irrelevance.
8. Increasing the prefix by one zero coordinate preserves nonempty common pools, not the empty support [0,c).
9. d=0 is vacuous, with no fabricated Fin(0) survivor.
10. The source→target induced map e is not needed in this local theorem; later apply at c=e(r), using genuine target zeros from merged #433.
11. The full code type p_j may impose mixed inequalities involving j, but canonical survivor values remain independent via zero extension of normalized witnesses.
12. This proves the immediate post-code survivor age, NOT its equality with the prescribed earlier survivor endpoint age R, which still requires finite-class numerical extraction.
13. It does not prove full pre-code F equality: the separate audited endpoint sandwich #472 combines the relevant endpoint values with legal zero-code.
14. No cover/split history, full Kpt L+/E diary, 24-case classification or global BRD lower bound follows.
15. Frozen black manuscript text is not altered; global history/BRD markers remain pending.

## Lean gate

Prove three named endpoints: genuine full old common-neighbour raw reindexing; complete physical canonical reindexing along any Fin e ↪ Fin d; zero-code survivor canonical identity along Fin.succAboveEmb j given genuine matching before-cut survivor type bits. Reuse the verified integer-witness reindexing and zero-cut theorems. Exact-head dedicated Lake build, strict standard-only axiom reports and full Lean CI required.
