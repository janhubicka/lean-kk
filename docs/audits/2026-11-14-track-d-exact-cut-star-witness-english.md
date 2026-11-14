# Track D: exact cut-star names for every upper vertex of a failed (B3) clique core
14 November 2026 — English-first proof and adversarial audit

## Aim

The already verified theorem henson_failedSelectedB3_has_eligible_cut_neighbour
gives ONE actual selected eligible original with a positive cut edge.
The existing henson_failed_selectedB3_has_cut_local_small_core classifies
ALL future vertices of ONE failed finite clique core, but its
conclusion records selected/relevant membership without retaining
the full next-cut L-type or free-level eligibility of that SAME name.

We strengthen these in one combined certificate. This is directly
useful for the remaining full-(B3)-loss / relative-profile comparison,
where a successor's admissibility is determined by complete L-reduct
types, not simply positive cut-neighbour membership.

## Generic lemma: exact named cut-crossing for every clique vertex

Fix arbitrary ordinary L-age test structures C,W in the single symmetric
graph language 1/0/1, a tested cut p, finite indexed source labels
original : Fin M -> Nat with predicate Selected, and a genuine
forbidden clique e : Fin ell -> Nat in W containing p. Suppose every
upper x>p in W has the COMPLETE induced L prefix type through p+1
of some Selected actual original v in C.

Then for every clique vertex e(a)>p there is a SINGLE v such that:

- Selected(v);
- C.binary p (original v) 0 = true;
- PrefixType_W(p+1,e(a)) = PrefixType_C(p+1,original v).

Proof. Choose the original v from the supplied complete upper-prefix
type for e(a). Choose b with e(b)=p. Since e(a)>p, b!=a. The
induced clique copy gives W.binary(p,e(a))=true. Apply congrArg to
the SAME chosen complete prefix-type equality at the named crossing
some(p),none; this gives W.binary(p,e(a)) =
C.binary(p,original v). Conclude the actual physical edge is true.
No information about W's future--future edges is transferred to C.

## Henson corollary: one finite core with all physical cut-star labels

Take any actual finite numerical H(E,k,N) whose base E is symmetric,
loop-free, K_ell-free (2<=ell<=k+1). At any cut p<N and any fixed
finite original-name family with arbitrary selected predicate Full,
assume the **genuine selected-stage full corrected (B3) fails**.

The checked henson_selectedB3_failure_has_small_clique_core yields
one bounded ordinary-L witness V and actual K_ell embedding e with:
(a) the exact same full old ordinary-L socle through p;
(b) V minus p avoids every normalized Henson forbidden pattern;
(c) V realizes K_ell and e includes p;
(d) every x>p in V is one of e's vertices;
(e) each such x has the complete p+1 L-prefix type of an actual
Full-selected original v with p+1 <= freeLevel_A(original v).

Apply the generic lemma to the selected predicate
Full(v) AND (p+1 <= freeLevel_A(original v)).
For every upper V-vertex x, use its witness e(a)=x and obtain ONE
Full-selected, cut-eligible, cut-ADJACENT physical original v whose
entire next-cut L-reduct equals the type of x. All five facts hold
simultaneously for the SAME finite V and e, not for separate cliques.

No no-(I2) assumption is needed for the witness extraction: a failed
B3 test already supplies the finite continuation and exact selected
upper types. No proof identifies the chosen original v with a macrodiary
ACTIVE vertex; q2-type auxiliary parameters are allowed and essential.

## Adversarial checks

1. The upper witness V is L-only: never assign auxiliary E to V.
2. Old initial socle equality includes every directed negative L atom,
   all unary/diagonal bits and carrier, not only positive graph edges.
3. Cut adjacency must come from the SAME v as the full prefix-type
   equality; combining two independent witnesses for v is insufficient.
4. The real source free-level guard p+1<=freeLevel(v) is preserved for
   the same v, even when many eligible sources share old full L+ types.
5. The proof does not assume no-(I2); its use would be redundant here.
6. Future--future edges of V may be arbitrary and are NOT asserted to
   coincide with edges among the named actual originals.
7. Generation zero works because the existing normalized Henson
   clique-core extraction excludes singleton and asymmetric failures.
8. The full future of the returned V is covered by the selected
   forbidden clique; this is stronger than obtaining one adjacent name.
9. The result gives at most ell-1 upper clique vertices, although
   source names may repeat across different x.
10. No fixed-prefix relative graph-age realization or converse
    B3-loss theorem is derived.
11. Neither occurrence-independent full source equality nor a common
    labelled inverse-source orbit follows.
12. The new module must compile at its exact head and pass a STRICT
    two-endpoint named axiom report: standard axioms only, no sorryAx.
    Avoid modifications to the central aggregate while parallel tracks
    continue to merge.
13. Manuscript black text stays frozen. Only an accurate short
    conditional summary may be added to olive prose after CI passes.

## Lean plan

Create Kk/B3ExactCutStarWitness.lean importing the verified
B3CutStarLocality and B3CutStarNormalForm modules. Prove the generic
label-preserving clique crossing lemma first, then the concrete
numerical-H failure specialization. Register both endpoints in an
isolated script/workflow and audit their true transitive axioms.
