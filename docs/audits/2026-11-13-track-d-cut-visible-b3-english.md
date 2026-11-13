# Track D — Cut-visible transfer for full corrected (B3)
13 November 2026 · English-first proof and adversarial audit

## Purpose and exact scope

The actual finite selected-stage B3 test in numerical H uses **complete L-reducts of chosen full L+ output records**, not just positive old-neighbour masks or selected diary vertices. The literal K4 cut-10 example in `Kk/K4FullVsMarkedB3.lean` disproves the unrestricted selected-only projection.

The useful narrower statement is **cut-visible profile dominance**. Let A be the genuine finite numerical-H partial structure of a symmetric loop-free K_ell-free original graph; C=A.L. Fix cut<N, a finite original-name pool `original : Fin M → Fin N`, and two selection predicates Full and Marked. Set `F=selectedStagePoolPrescribedData A cut original Full`, `G=selectedStagePoolPrescribedData A cut original Marked`.

Assume:
1. **A marked source exists**: some S belongs to G.source. The conclusion would otherwise be vacuous on the marked side.
2. **Cut-visible complete-output coverage**: for every Full-selected name v whose actual C-edge from cut to original(v) is true, the *full complete (cut+1) L-reduct* of v equals `(G.target T).lReduct` for some actual `T ∈ G.source`. This is about G's genuinely chosen source representative, not merely `Marked v`, and does not infer auxiliary E on an age-test continuation.
3. G satisfies corrected B3 for the normalized Henson family.

**Claim.** F satisfies corrected B3 for the same family. Equivalently, failure of F forces failure of G under (1)–(2).

### English proof

Suppose F fails. Apply the checked `henson_selectedB3_failure_has_small_clique_core`. It supplies a finite ordinary-L model V with exactly the actual old C-socle through cut, no forbidden pattern after deletion of cut, and a forbidden K_ell copy e containing cut. Every vertex x>cut of V is one of e's vertices. Its complete type through cut+1 is the complete L-type of some Full-selected original v with the genuine free-level guard.

Since the forbidden clique includes cut, V has `L(cut,x)=true`. Equality of the complete prefix type, including BOTH directed cut-crossing atoms, implies `C.L(cut, original(v))=true`. By assumption (2), the complete upper type of x is among G's genuinely chosen output L-reducts. This holds for EVERY upper vertex of V.

Pick a marked source S from (1). Its complete target is extracted from an actual original in A by `selectedStagePoolPrescribedData_source_original`. The checked `ambient_partialType_prescribedSocle` proves its prescribed ordinary L-socle agrees with C through cut. Hence V has the same old ordinary L-socle as `G.target S`.

All hypotheses of G.CorrectedB3 now hold for V: bounded carrier; same old socle; every upper type in G's actual L-reduct image; no forbidden copy after deleting cut. Apply G.CorrectedB3 to the normalized K_ell pattern realized by e. Contradiction.

### Hostile audit / false shortcuts excluded

- **Not all selected names:** the entire upper type spectrum of F need not be included in that of G. Only the named complete upper L-types adjacent to cut are required. The small forbidden-clique core is essential for this weakening.
- **Not just names:** `Full v ∧ Marked v` is insufficient for target equality. Several originals may have identical old full L+ source records while their next L columns differ; the source-map implementation chooses an arbitrary representative for each fibre. Condition (2) explicitly requires the actual *chosen target* to match.
- **Not just edge masks:** a common positive cut-neighbourhood is insufficient; all negative and directed old L atoms and singleton data in the (cut+1)-type must match.
- **No invented E:** the witness V is an arbitrary L-only model; future–future edges may be freely chosen. The argument only reads the already prescribed crossing L column to the tested cut.
- **Not the general normalized-language theorem:** the inference uses that for symmetric loop-free K_ell-free numerical H, every failed normalized-family corrected B3 yields a K_ell clique core even at generation zero. It does not apply to arbitrary forbidden relational patterns.
- **No global statement:** The physical diary still needs to prove the cut-visible target coverage for the *entire parameter closure* and compatibility across two occurrences. It also needs the actual full f_ell identification and the common labelled inverse-source orbit. None is inferred.
- **Source nonemptiness:** if G.source is empty, G.CorrectedB3 is vacuous. Do not drop hypothesis (1) without separately deriving it from a genuine upper clique witness and (2).
- **Strict cutoff:** the cut+1 type, not merely the cut type, carries the tested crossing atom. Replacing cut+1 by cut loses the decisive edge.
- **Quantifier check:** the coverage premise is uniform over all Full-selected names with a real positive cut edge, not just the names occurring in a particular proposed canonical witness.

## Lean validation gate

Implement the claim in a new dedicated `Kk/B3CutVisibleTransfer.lean`, importing the proven small-clique-core theorem and the true selected-stage source predicate; retain exact explicit hypotheses. Register a dedicated strict transitive-axiom report and compile this **new module explicitly** (it is not in `Kk.lean` to avoid collisions with parallel Track A/B/C/E/F work). Keep any paper-level validation marker BLUE until a genuine numerical-H full parameter-closure coverage theorem and hosted kernel check both exist. Do not modify protected black manuscript text.
