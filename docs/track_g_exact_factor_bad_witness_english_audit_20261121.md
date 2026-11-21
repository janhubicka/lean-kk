# Track G — actual witnesses for every exact-factor Bad cut

21 November 2026. English-first proof and adversarial audit. Depends on the separately verified G426 exact factor-Bad predicate; do not declare this note Lean-validated before the new source passes.

## Theorem: a finite bad cut has a concrete new-source obstruction

Fix one actual Kpt AlgorithmRun RX on X, cut c<top genuinely BORING in RX, and one independently exhaustive finite index `(node,live)` of a complete target source at c. Assume c lies in `kptExactOldFactorBadCuts`.

Choose the genuine OLD skip-only total MMap D_c supplied by RX.noninteresting_step at c. Then RX.F(c)=RX.F(c+1)∘D_c and one of the following PHYSICAL witnesses exists:

(T) a live target index j whose actual Kpt node ends exactly at c (new terminal I1);
(M) two live target indices j,k whose actual nodes are in the same component and have meet level c (new I2);
(F) a live target index j crossing c for which D_c(node(j)|c) ≠ node(j)|(c+1), a violation of the unique old full-source total skip factor.

This gives one old factor D_c and one finite explicit obstruction, rather than a vague failure of universal compatibility.

## Proof

Take D_c from RX.noninteresting_step at c. Suppose none of T/M/F occurs. Then every live index has level ≠c and no live pair realizes an I2 meet at c. All crossings of live nodes satisfy the actual equation for D_c. Any other total MMap E with the same old F factorization is equal to D_c by the verified left cancellation `kpt_MMap_comp_left_cancel`: RX.F(c+1)∘E=RX.F(c+1)∘D_c. Thus E also satisfies every target crossing. The three clauses defining `KptIndexedOldFactorCompatibleAt` all hold, contradicting the membership of c in exact Bad. Therefore at least one witness exists.

## New-only nature of the witnesses

Because RX is genuinely BORING at c, no actual old full-source terminal exists at c, no two old source nodes have an I2 meet at c, and D_c satisfies every old full-source crossing. Therefore:

- a T witness is a target terminal absent from the old complete closure;
- an M witness cannot consist of two old-source nodes (at least one is outside old source);
- an F witness cannot itself be an old-source node. More strongly, its COMPLETE paired lower/upper Kpt ancestor record cannot already be witnessed by one old crossing node: otherwise the old crossing equation for D_c would force the same upper ancestor, contradiction.

These facts remain true in a genuine nested seed extension X⊆Y. One cannot replace 'new-only' with 'not an old final index': early-activated old-final names may be new LIVE and cause an obstruction.

## Why this matters

This turns the exact factor-Bad predicate into an I1 terminal, I2 pair, or a single-node full Kpt factor-disagreement witness. It is a useful input for the previous Track G single-node novelty interval and successor-level envelope arguments. However it does NOT give a diary-uniform bound on how many such nodes or cuts occur; that requires a resolved construction and tracking each dependent L+/E source history.

## Adversarial checks

1. The theorem requires an ACTUAL old-boring cut; a generic cut can have no prescribed factor D_c.
2. The live index must be exhaustive on the full dependent parameter/meet target source at c.
3. Finite names may repeat; witness validity does not require an index bijection or injective presentation.
4. The D_c chosen from the old run is unique as a total factor of the old F step; its SkipOnly property is genuine.
5. Clause F compares actual complete Kpt ancestors, not ordinary graph ages or separate lower/upper spectra.
6. A terminal at level c does not cross above c, so T must be tested separately.
7. An actual I2 meet needs both target nodes and the real same-component relation; no I2-free assumption.
8. An F witness may share its OLD ancestor with an old node but have a distinct UPPER ancestor; it is then not captured by an old full crossing PAIR.
9. New final vs newly activated old final names must not be conflated.
10. The witness extraction is classically finite but not a uniform algorithm for total MMaps.
11. At a genuinely old interesting cut the exact Bad set does not count it; K4 auxiliary cuts such as 10 and 22 remain genuine.
12. A witnessed bad cut need not show the refined diary theorem is false; it identifies the needed exceptional microevent.
13. No chronological coordinate transport, prescribed infinite resolved H+, common labelled inverse source or sharp BRD numbers follow.
14. The old-factor Bad support is exact for synchronized run I/F, but its cardinality can still depend on physical source size.

## Lean protocol

After G426 merges, import it and G398. Prove one exact cut witness theorem and the stronger new-only/full-pair novelty consequences using genuine old noninteresting-step laws. Check exact-head compiled source and named standard-only axiom reports independently. Keep black manuscript frozen.
## Formalization scope

First directly compile two theorem endpoints: (i) each exact Bad cut has a concrete indexed I1/I2/old-factor mismatch witness; (ii) a mismatch of the actual old total factor cannot share the COMPLETE paired old/upper ancestor record of any genuinely old crossing. Then investigate finite source-locality of the other witness cases. The second theorem requires no target index; it uses genuine old-step crossing plus total left cancellation.
