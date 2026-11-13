# Track B — common ambient old-socle bridge (13 November 2026)

## Exact improvement over the generic profile-gap audit

The general necessary-condition theorem in `Kk/B3ProfileGapAudit.lean` distinguishes two possible failures of marked-to-full corrected-(B3) transfer: missing *old ordinary-L socle* coverage or missing *complete upper L-reduct* inclusion. For profiles actually extracted from **two finite original-name pools in ONE ambient enumerated partial structure A**, and for a nonempty marked pool, the first alternative is automatically impossible.

Fix an arbitrary ambient `A : EnumeratedPartialStructure db du dd`, a cut `p<A.size`, finite indices `fullOriginal : Fin M → Nat` and `markedOriginal : Fin N → Nat`, and one genuinely present marked name `w : Fin N`. Let
`F := ambientPoolPrescribedData A p fullOriginal` and
`G := ambientPoolPrescribedData A p markedOriginal`.
The actual successor-tree construction chooses the output of each old source type from **one of the original names which realizes that source**, even when multiple names share the same old type.

### Concrete theorem A: full-to-marked old L-socle coverage

For every `S∈F.source`, choose the actual original `v : Fin M` supplied by the existing verified theorem `ambientPoolPrescribedData_target_original`. Thus
`F.target S = A.partialTypeAt (p+1) (fullOriginal v)`.

Choose `T = A.partialTypeAt p (markedOriginal w)` in G.source, and obtain the actual chosen target representative `u : Fin N` for T from the same successor-tree theorem.

The verified `ambient_partialType_prescribedSocle` gives both
`SameInitialL (prescribedOrdinarySocle (A.partialTypeAt (p+1) (fullOriginal v))) A.L p`
and
`SameInitialL (prescribedOrdinarySocle (A.partialTypeAt (p+1) (markedOriginal u))) A.L p`.
Reverse the latter equality **componentwise** (carrier, all ordered binary, unary, diagonal atoms), and compose by `SameInitialL.trans`. Therefore every full old source has a same-socle marked representative. No agreement of the *type vertices* or E bits is needed, nor is injectivity of the original-name maps.

### Concrete theorem B: full failure forces an extra upper type

Assume also `¬F.CorrectedB3 family` and `G.CorrectedB3 family`. Apply the already compiled generic `fullB3_failure_good_marked_missing_upper` to the coverage theorem A. Conclude that there is a **complete upper ordinary-L reduct permitted in F but not in G**.

This reduces *one branch* of the full/marked transfer obstruction to explicit upper-type classification whenever both prescribed source functions are genuinely formed from original pools of the same ambient A. In the actual finite K4 gadget the auxiliary q2=22 upper reduct supplies such a missing type.

## Adversarial checks

1. The ambient model must be the SAME `A` on both sides. Two unrelated abstract source functions do not share a common old L-socle.
2. Marked nonemptiness is essential. It is witnessed by `w:Fin N`, not hidden behind a false general claim for `N=0`.
3. The cut bound `p<A.size` is essential for the actual initial-carrier equivalence. It is explicitly assumed, rather than inferred from arbitrary `original` indices.
4. The source output is `ambientPoolTarget`, whose chosen representative may be different from `w`. Obtain its existence from the existing theorem instead of assuming the two names coincide.
5. Both upper profiles are complete prescribed L-reduct families. The result does not project away newly available auxiliary upper types.
6. Transitivity needs the marked socle equivalence in the REVERSE direction. It must be reversed for all four `SameInitialL` fields, including false atoms.
7. This is a theorem about actual finite **ambient pools**. It does not prove the ACTUAL Algorithm 5.4 parameter-closed I3 source equals such a pool; that source-identification premise remains open.
8. A source map may have repeated original indices or multiple original vertices representing the same old type. The proof does not use injectivity.
9. A fixed ambient old L-socle does not make upper–upper edges of an arbitrary corrected-B3 witness match the ambient graph; the forbidden-copy continuation still has freely chosen upper edges.
10. The result is independent of graph-specific K_ell avoidance, so it covers any normalized forbidden family without misclassifying loop/asymmetry obstructions as cliques.
11. The existing finite K4 example is a positive check for the missing-upper conclusion, not evidence that the full resolved diary was correctly realized or has the proposed exact degree.
12. Neither theorem proves the full global profile equality, full relative-profile fidelity, or common labelled inverse-source orbit. The manuscript-wide corrected-(B3) projection remains pending.

## Verification

English proof above committed before the Lean module. Proposed two named endpoints: `ambientPool_full_to_marked_Lsocle_coverage` and `ambientPool_fullB3_failure_requires_extra_upperL`. Together with the three already exact-head-CI-verified generic endpoints of PR #95, the new exact-head gate will have **408** standard-only axiom reports, a full `lake build`, and parser self-test. No global green manuscript marker.
