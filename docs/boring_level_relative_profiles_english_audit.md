# 12 November 2026 — English-first adversarial repair: boring levels require faithful relative profiles

**Affected passage:** the editable olive proof and hypothesis list of `Lem:Kk_Boring_Level` in `kk.tex`. All protected black prose remains unchanged. This audit is committed **before** Lean formalization.

## Failure in the previous proof

The proof appealed to Lemma `Lem:Extension_Profile_Determines_Age` in two places. In the reverse direction it said: if the selected graph-age F changes, the extension-profile lemma supplies a labelled clique that was **admissible over the old base before inserting the level** and inadmissible afterwards. That inference is unjustified. The extension-profile lemma supplies an **abstract feasible labelled clique pattern** in the sorted class K_F. A pattern can be feasible as a standalone graph yet fail to have any relative realisation over the *complete prescribed old L neighbourhood*.

**Counterexample:** in a triangle-free graph let p be a fixed old vertex, and demand that two proposed new vertices q,r both be adjacent to p. The two-vertex complete clique {q,r} is abstractly triangle-free, but it cannot be realized with all three required edges p–q, p–r, q–r. The old proof's “successive one-point extensions” move is invalid without the exact finite old-neighbourhood test.

The forward direction also needs an identification: projecting the future vertices of a full forbidden clique into selected active sorts is not by itself a proof that the before/after **relative** admissible profile equals the abstract feasible-vector system of F at either stage. The original witness-projection hypothesis handles source projection; it does not alone establish full relative realisability.

## Correct conditional statement

At one nonstructural candidate level, let F_before and F_after be the **genuine graph-age functions** on the fixed labelled selected sorts, on the two sides of inserting the level. For each normalized labelled clique vector w (total size at most ell−1), let:

- Rel_before(w): the complete prescribed old finite L+ source configuration (including all relevant auxiliary E/parameter records) permits a compatible L-only continuation of precisely w at the stage before inserting the candidate level;
- Rel_after(w): the corresponding compatible continuation exists after inserting that level.

The distinction between *the entire source configuration* and the selected shadow is essential. Add the following **relative-profile fidelity** hypothesis for BOTH stages:

[
mathrm{Rel}_{m before}(w)
 iff winmathrm{Feasible}(F_{m before}),qquad
mathrm{Rel}_{m after}(w)
 iff winmathrm{Feasible}(F_{m after})
]
for every normalized labelled w, where `Feasible(F)` tests **all** support bounds as a joint system.

Also require **no creation of new relative extensions** on insertion:
[
mathrm{Rel}_{m after}(w) Rightarrow mathrm{Rel}_{m before}(w).
]
Finally, under absence of (I1),(I2), the automatic (B1),(B2), and the existing clique-witness/source-projection hypotheses, the full corrected (B3) test must fail **exactly if** some normalized w is permitted before and forbidden after:
[
mathrm{B3Fails} iff exists w,(mathrm{Rel}_{m before}(w)land
            
eg mathrm{Rel}_{m after}(w)).
]
This last equivalence must eventually be **proved for the particular numerical-H construction**; it cannot be inferred from abstract graph-age data or the unlabelled set of source upper L reducts.

## Repaired proof

The new Lean theorem `integerGraphAge_eq_iff_same_feasible_vectors` (locally checked; pending exact hosted CI when this note was written) states that for genuine graph ages, **the full feasible normalized labelled vector profile determines F**, in both directions.

Under relative-profile fidelity,
[
F_{m before}=F_{m after}
iff orall w;(mathrm{Rel}_{m before}(w)
       iffmathrm{Rel}_{m after}(w)).
]
Under the no-new-relative-extensions condition, inequality of these profiles is equivalent to existence of a lost relative witness. Under the complete corrected-(B3) source bridge, that is exactly a (B3) failure. Since the structural (I1),(I2) events are excluded and (B1),(B2) hold, the Boring Extension Lemma identifies boringness with absence of (B3) failure. This completes the **conditional** criterion without smuggling in physical realisation.

## Hostile checks

1. **Relative vs abstract:** a feasible clique pattern need not embed over a prescribed old prefix. The p–q–r triangle example refutes the shortcut.
2. **Two stages:** fidelity must hold before AND after insertion. Having it only on one side gives no profile comparison.
3. **Joint bounds:** use `∀ T` on all integer supports; canonicalization cannot be applied to each raw bound separately.
4. **Total-size bound:** the normalized vector type includes only size≤ell−1. Full forbidden patterns must be reduced to these finite future parts by the corrected source-witness argument.
5. **Parameter records:** the relative-continuation predicate must retain full old L+ source and dependent Kpt parameter data; the selected shadow is inadequate.
6. **No new feasibility:** an iff between age inequality and *loss* of witnesses needs after⊆before. Otherwise an age change could result from newly enabled patterns.
7. **B1/B2 and I1/I2:** their handling remains separate. An absent B3 obstruction does not by itself mean a level is boring when it is structural.
8. **Full source assignments:** equality of an unlabelled spectrum of possible upper L reducts does not imply equality of complete L+ types *assigned per labelled source node*.
9. **Realised W vs all w:** a finite future W might fail to realize one abstract feasible vector, even if the profile on W contains all selected top-originals already present.
10. **Existing counterexample:** the verified K4 two-cut numerical-H gadget has a genuinely interesting auxiliary (I3) microlevel while the selected F-state is unchanged. The added fidelity/B3-projection bridge is not automatically satisfied by it; no contradiction with the conditional criterion follows.
11. **Source comparison:** even identical full B3 profiles for two occurrences would not alone prove a common labelled inverse-source orbit without the actual monoid/envelope map.
12. **Logical boundary:** merely *assuming* the B3-loss equivalence makes a conditional proof easy. The genuine mathematical work is deriving that equivalence from the complete numerical-H construction; treat it as an explicitly open obligation, not a green theorem about that construction.

## Planned formalization

Once the exact abstract feasible-vector theorem passes its hosted gate, prove two finite Lean lemmas over the existing `IntegerGraphSupport`/`IntegerCliqueWeights` APIs:

A. If two genuine ages have faithful relative predicates before and after, equality of their age functions is equivalent to equality of the relative predicates **pointwise on all normalized vectors**.

B. Under monotonicity after⊆before, age inequality is equivalent to existence of a lost relative vector.

This is an abstract but nontrivial interface check. It does NOT validate the actual Henson relative-profile fidelity or the full corrected-B3 loss equivalence. Mark only those conditional endpoints green after full Lean CI; leave the global boring-level result and resolved-copy application pending.

## Change contract

Edit only the olive theorem statement/proof portion, and add an inline scope note if necessary. Avoid rewriting any protected black passage or re-adding previously removed TODOs. In particular, do not mark the unbounded resolved Henson copy or the common labelled orbit validated.
