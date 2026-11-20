# Track G — the EXACT finite old-factor Bad-cut certificate

20 November 2026. English proof FIRST; nineteen adversarial checks prior to Lean.

## Inputs and verified background

Fix one normalized Kpt family, literal nested actual seeds X⊆Y, scan top t,
and ONE genuine AlgorithmRun RX on X. The target run is NOT assumed.
Let `node : Fin Q → Kpt` and Boolean `live(c,j)` enumerate EXACTLY
the complete target candidate closure `C_Y(c)=closure(S,RX.I(c+1),Y)`
for each c<t, including all generated meets and dependent parameters.
No OLD finite index is needed: the actual RX already gives every old
boring-step map, and total left-cancellation makes its factor unique.

## Definition (exact per-cut factor compatibility)

For a cut c and the target index, `IndexedOldFactorCompatible(c)` means:

(T) Every live target name j has level different from c;
(M) No two live target names j,k are SameComponent with meet level c;
(F) For EVERY total genuine MMap D satisfying

     RX.F(c) = RX.F(c+1) ∘ D,

    and every live target name j crossing c, the exact complete
    Kpt ancestor equation holds:

     D(node(j)|c) = node(j)|(c+1).

Clause F is a test of a UNIQUE factor at every OLD-BORING cut:
RX.noninteresting_step supplies D, and the verified G309
`kpt_MMap_comp_left_cancel` proves uniqueness from total F endpoints.
Thus no arbitrary new step choice is hidden in this condition.

## Definition (exact canonical factor-Bad set)

Let `ExactFactorBadCuts` be the finite subset of `[0,t)` containing
exactly those OLD-BORING cuts c for which
`IndexedOldFactorCompatible(c)` fails. This is a Finset defined
by classical filtering of `[0,t)`; it does NOT claim the monoid
or the full dependent Kpt index is effectively enumerated.

## Theorem A (exact characterization)

Under the single exact target source-index hypothesis,

  ExactFactorBadCuts = ∅
      iff there EXISTS an actual AlgorithmRun RY on Y
         with RY.I=RX.I and RY.F=RX.F as TOTAL functions.

Proof, left-to-right: at each old-boring cut c, emptiness yields
T/M/F. Exactness of the finite index converts no live j of level c
to no genuine target terminal, and no live pair with meet level c
to no genuine target I2 fork. RX.noninteresting_step at c gives
the actual old skip factor D, skip-only, its full old crossing law
and the precise original total F factor equation. F applies to D;
exact index representation converts all its target live equations
to the actual full candidate source. Use the verified G398
`actualRun_transport_iff_old_boring_original_factor_extends`
to construct the whole synchronized target run.

Proof, right-to-left: G398's necessity gives absence of target I1
and I2, and says every genuine old step factor respecting its actual
old crossing law also respects the complete target closure.
At a fixed old-boring cut, choose RX's genuine step factor E.
Every other total D with RX.F(c)=RX.F(c+1)∘D equals E by G309
left cancellation, whether or not the defining F clause
explicitly mentions old crossings or skip-only. Hence D obeys
every target indexed equation. The finite certificate holds
at each old-boring cut, so the exact Bad Finset is empty.

## Theorem B (least-support / index-independence)

For a fixed actual RX and candidate target Y, any TWO independently
exact finite target indices have the SAME exact factor-Bad Finset.
Proof: the three clauses T/M/F are statements about source membership
and actual Kpt nodes, and an exact index is just a surjective
enumeration of that stage's complete candidate source. The old
factorization and selected tails are identical, and no choice of
finite names changes truth of any clause.

In particular this is an intrinsic finite CUT support, not an
artifact of enumerating the target source or choosing a skip factor.

## Relation to earlier E54 canonical no-novelty Bad set

On an actual nested Kpt extension with independent exact OLD and
NEW indices, the exact factor-Bad support is INCLUDED in the
older E54 canonical no-novelty Bad support at the same old cuts.
No-novelty implies no new terminal (since an old boring source
has no terminal) or I2 meet (because any new I2 would force
new full crossing nonfunctionality), and ensures the uniquely
determined old factor satisfies all new crossing constraints.
Strict containment is possible in principle: a new full crossing
pair may violate no-novelty yet still obey the old factor.

The theorem's exact equality is stronger than the earlier
zero-E54-Bad sufficient condition. Do NOT assert strict
containment for an actual numerical-H+ example without constructing
one. The primary formal target is theorem A.

## Adversarial checks

1. The source index must represent ALL of closure(S,RX.I(c+1),Y),
   not only selected original vertices or the graph-age shadow.
2. Only ONE target index is assumed; old index is unnecessary.
3. Distinct finite indices may have different Q cardinalities.
4. An index need not be injective for the equivalence; exhaustive
   membership at each cut suffices. No index bijection required.
5. Live-mask checks are on RX.I tails, NOT the unknown Y-run I tails.
6. The 'factor' quantifier covers full genuine MMaps, not
   automorphisms of an ordinary graph or finite quotients.
7. The quantifier is unique at old-boring cuts by G309 cancellation;
   it is NOT vacuous because RX.noninteresting_step supplies D.
8. Exact F equality must be a TOTAL MMap equation, not equality
   restricted to observed source nodes.
9. I1 is terminal existence; full crossing relations miss terminals.
10. I2 uses actual same-component meet; do not replace by just
    a nonfunctional ordinary-L selected shadow.
11. For a terminal j at c, the F crossing test does not apply;
    T is an independent obstruction.
12. Auxiliary E and negative L are retained by the actual
    Kpt ancestor nodes in F, not projected away.
13. Interesting OLD cuts are excluded from Bad; old interesting
    cuts remain interesting by source monotonicity X⊆Y.
14. The Finset only bounds number of cut coordinates by top;
    it does not yield a bound independent of physical N/top.
15. `noncomputable def` plus classical decidability does not
    claim an executable enumeration of all MMaps.
16. K4 genuine selected auxiliary cuts 10 and 22 remain
    part of the actual scan; this theorem cannot erase them.
17. No labelled inverse-source node correspondence follows
    even if the exact Bad set is empty.
18. No cross-occurrence chronological coordinate map,
    corrected B3 versus relative continuation, resolved
    infinite H+ copy or unavoidability/lower BRD follows.
19. The older E54 Bad may be strictly larger; no counterexample
    is claimed until actual physical witnesses are formalized.

## Lean acceptance

Create a standalone Kk exact factor-Bad module importing G398,
E54 and the finite Kpt index interface. Prove
1) exact finite Bad membership,
2) empty Bad iff an actual same-I same-TOTAL-F run exists,
3) if practical, intrinsic index-independence.
Use dedicated strict same-head Lake build and qualified standard-only
named #print axioms reports, plus independent full Lean build.
Do not modify frozen black manuscript or promote global BRD.
