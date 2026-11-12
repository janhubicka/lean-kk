# 12 November 2026 — adversarial repair: what the extension profile actually determines

**Scope:** the editable olive passage surrounding Lemma `Lem:Extension_Profile_Determines_Age` in `kk.tex` (current branch PR #22), not any protected black text. This is the English proof and adversarial audit **before** new Lean formalization. The theorem's numerical equality is sound; its last proof sentence was too strong without a relative-realization hypothesis.

## Exact corrected statement

Fix `ell≥2`, a finite set of labelled sorts D, and a **genuine** normalized integer graph-age function F on all nonempty supports T with 0<|T|≤ell−1. The abstract extension profile consists of all labelled *complete clique patterns* whose nonnegative multiplicity vectors `w:D→N` obey

`sum_D w ≤ ell−1`, and `sum_{j∈U} w_j ≤ F(U)` for EVERY admissible nonempty support U.

For each T, the largest size of a feasible pattern whose vertices all have labels in T equals F(T). The graph-age consistency axiom supplies the lower-bound pattern, supported in T; the T-inequality supplies the upper bound. Therefore if two genuine graph-age functions F,G have the same **entire set** of feasible labelled normalized vectors, then F=G pointwise, and conversely pointwise equality gives identical profiles.

**This statement is about the abstract age of permitted labelled clique patterns**, not all cliques actually realized over an arbitrary fixed finite old graph in a concrete Henson extension. An abstract feasible pattern is not automatically a compatible relative extension of a particular past P.

## Explicit correction to the English proof

The old sentence `Such a clique can be exposed by F(T) successive one-point extensions.` was ambiguous, and, when read as an extension **over the already fixed old graph with additional required neighbours**, unjustified. The repaired proof says:

> The consistency witness is the multiplicity vector of a formal labelled complete graph on F(T) fresh vertices. Its feasibility proves membership in the abstract D-sorted age K_F. Realising it above a *specified* old Henson prefix while prescribing all past-to-future L atoms requires checking each full old neighbourhood; it is not implied by the present profile lemma.

This correction preserves the numerical lemma, avoids weakening its genuine abstract-age content and removes the unsupported physical inference.

## Adversarial checks

1. **Relative obstruction:** take ell=3, old vertex p, and two future vertices q,r with required edges p–q and p–r. An isolated 2-clique {q,r} is a legitimate abstract triangle-free graph, but adding q–r to this fixed adjacency column makes the triangle pqr. Thus the abstract 2-clique does not automatically realise the prescribed extension over P.
2. **Joint versus individual constraints:** the feasible witness condition quantifies over **every** nonempty support. The canonicalizer G_B preserves this joint condition for each normalized vector; it need not preserve each individual bound B(T) separately when B is not an age. The statement here assumes genuine F and G.
3. **Multiplicity:** labelled complete patterns can have multiple vertices of one sort, so the profile is a set of integer vectors, not a set of occupied sort subsets.
4. **Total bound:** the normalization `sum_D w≤ell−1` is essential for comparison with the actual `IntegerCliqueWeights` API. The proof from F uses the supported consistency witness of size F(T)≤ell−1.
5. **No blank-support confusion:** T ranges over `IntegerGraphSupport d ell`, excluding ∅; the convention F(∅)=0 is only auxiliary. If d=0, the family of supports is empty and equality of the unique empty age functions is vacuous.
6. **Small ell boundaries:** the manuscript's Henson setting has ell≥3; the Lean lemma can use the exact existing support subtype without fabricating additional values for ell=0.
7. **Full profile matters:** equality of the possible *maximum* size on one distinguished T does not imply F=G; equality is needed for all T (or equality of entire feasible-vector systems).
8. **Not full B3:** even a perfect ordinary-L age profile does not determine auxiliary Kpt E, parameter closure, assigned L+ successor types at every I3 source, or a common labelled inverse-source orbit.
9. **No fixed-pool surjectivity:** the empty future pool W has no singleton witness, although a normalized singleton vector may be feasible in the abstract age. This is already guarded by `oneSortOneWeight_not_from_empty` in merged `lean-kk`.
10. **Finite realization remains a separate theorem:** the current merged free-amalgamation result combines already compatible extensions; it does not create the necessary individual complete old-neighbourhood certificates. The proposed universal typed clique gadget is ordinary-L and does not by itself solve relative Henson/H+ realization.

## Lean plan

Add directly to the genuine `IsIntegerGraphAge` and `integerGraphAgeCanonical` APIs:

(A) `integerGraphAge_eq_sup_feasible_vectors`: for all genuine F and supports T, F(T) equals the maximum of `integerCliqueOnSupport w T` over **all** normalized w respecting F.

(B) `integerGraphAge_eq_of_same_feasible_vectors`: if F,G are genuine graph ages with precisely the same set of feasible normalized vectors, then F=G.

(C) Optionally, a reusable exact criterion equating the suprema of two arbitrary raw bound systems B,C when their feasible-vector systems agree; this is canonicalization, not equality of raw B,C.

Write the proof with no `sorry`, extra axioms, or independent age assumption beyond the existing genuine graph-age hypotheses. Perform the full pinned build and strict named axiom audit; only then add precise green theorem markers, never a global claim that the bounded resolved copy or B3 comparison has been proved.

## Protected prose and change contract

Only editable olive text around the extension-profile lemma is repaired. All protected black prose remains byte-for-byte unchanged. Green verification marks elsewhere remain unchanged until the new source passes hosted CI.
