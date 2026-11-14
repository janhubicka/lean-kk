# Track E — actual new-root closure absorption from proved seed monotonicity

**14 November 2026. English proof and adversarial checks BEFORE Lean.**

Stacked on Track C's independently exact-head verified, still draft [PR #192](https://github.com/janhubicka/lean-kk/pull/192), branch `kk-track-c-new-root-closure-absorption-20261114` head `b38d1dc5f0d5c1bca286cb92cb693ab52e8f0982`. Track E's genuine seed-monotone AlgorithmRun theorem has already merged into main in [PR #181](https://github.com/janhubicka/lean-kk/pull/181), whose [isolated 14/14 CI](https://github.com/janhubicka/lean-kk/actions/runs/43615340310) and [full CI](https://github.com/janhubicka/lean-kk/actions/runs/43615340305) passed. This is a new independent Track E integration step and does not edit Track C's proof or the protected manuscript.

## Mathematical gap closed

Track C's actual physical new-root construction has the **corrected original-only form**

`Y = closure_(S,I)(X) ∪ O`,

where `S=admissibleKptSTree family` and `O` is the image of genuine NEW physical `finiteNumericH L k M` Kpt original nodes. **It is NOT the entire new-root prefix pool**: the superseded all-prefix seed construction forces every earlier level into (I1).

The independently checked Track C closure-absorption theorem states that for any selected set J CONTAINING the inherited old selected levels I,

`closure_(S,J)(Y) = closure_(S,J)(X ∪ O).`

Its real pre-cut specialization used a separately **assumed** inclusion `I⊆RunNew.I(c+1)`. But Track E #181 proves this inclusion **from the ACTUAL dynamics**, when I was already selected by the previous same-top AlgorithmRun.

### E38. Remove the new-run higher-level retention hypothesis

Fix two actual AlgorithmRuns in the same normalized Kpt monoid and **same source horizon top**:

- `RunOld` on the genuine old Kpt seeds `X`;
- `RunNew` on the corrected physical `Y=closure_I(X) ∪ O`, with O the set of genuine new admissible Kpt original nodes from finite `H^+=finiteNumericH L k M`.

At a true pre-cut c<top, suppose the inherited generating levels lie in the actual OLD higher selected set:

`I⊆RunOld.I(c+1)`.

There is **NO hypothesis** that I survives in the new run.

**Proof.**
1. The genuine closure constructor guarantees `X⊆closure_I(X)⊆Y`. No physical graph-age approximation is involved.
2. The verified Track E theorem `actual_AlgorithmRun_selected_levels_mono_of_seed_growth` applied to the TWO real Kpt runs on X⊆Y gives `RunOld.I(q)⊆RunNew.I(q)` for EVERY q≤top.
3. At q=c+1, use c<top to deduce `I⊆RunNew.I(c+1)`. This discharges precisely Track C #192's missing premise.
4. Invoke its checked `finiteNumericH_newRoot_closure_absorption` at J=`RunNew.I(c+1)` to obtain the **LITERAL equality of the two entire physical Kpt pre-cut closures**:
[
  \operatorname{cl}_{\mathrm{RunNew}.I(c+1)}(\operatorname{cl}_I(X)\cup O)
  =
  \operatorname{cl}_{\mathrm{RunNew}.I(c+1)}(X\cup O).
]
5. Because the actual node sets coincide, the genuine (I1), (I2), full old-to-upper `L^+` crossing relation (with negative atoms, auxiliary E, meet and parameter nodes, and possible nonfunctional I2 forks), **and** the actual (I3) monoid-level no-skip verdict coincide on the nose. There is no corrected-(B3) or no-(I2) assumption.

This does NOT show that adding new originals preserves the complete previous **selected-level set**; it shows that preinserting the old selected-parameter closure cannot itself create an additional event at the specified cut, beyond what the BARE old+new original seed closure would generate.

### E39. A historical selected-level formulation

More convenient to the resolved-copy schedule: if `I⊆RunOld.I 0` and EVERY q∈I satisfies c<q, then the verified final-tail identity
`RunOld.I(c+1) = \{q\in RunOld.I0 : c<q\}`
establishes E38's old-higher hypothesis. Thus literal physical source/event comparison follows **without** separately assuming old-level retention in `RunNew`.

The strict inequality c<q is indispensable! An inherited selected level ≤c need not be available in the new pre-cut level set `RunNew.I(c+1)`, even if it survives globally in `RunNew.I0`. Preinserting its old generated parameters might therefore change the pre-cut closure.

### E40. A completely CONSTRUCTED per-cut canonical application

Take an arbitrary actual old Kpt AlgorithmRun `RunOld` on X at top and a specific c<top. Choose the inherited generating set **canonically as the OLD actual higher levels**
`I := RunOld.I(c+1)`.

Form the correct physical new-original-only seed set `Y_c := closure_I(X) ∪ O` (the source depends on the chosen cut). Construct the new run
`RunNew_c := canonicalAlgorithmRun (normalizedKptSMTree family) Y_c top`
using the already verified actual generic run constructor. Then `I⊆RunOld.I(c+1)` is reflexive. E38 proves without ANY added new-run-retention hypothesis that
[
 \operatorname{cl}_{\mathrm{RunNew}_c.I(c+1)}(Y_c)
 =
 \operatorname{cl}_{\mathrm{RunNew}_c.I(c+1)}(X\cup O).
]

This is a **real physical per-cut seed/run theorem**, and completely compares I1/I2/I3 and full dependent L+ pre-cut data between preinserted and bare new-original seed representations. It is NOT a theorem about one fixed Y used across ALL cuts: here Y_c depends on c. The global unbounded resolved diary must still explain which prior generating I levels are higher than each cut.

### E41. Every newly selected cut has a witness in the BARE seed closure

Under E38, suppose `c∈RunNew.I c` but `c∉RunOld.I c`. The merged Track E new-cut physical theorem produces either:
- an actual **new** terminal Kpt node at c of `Z_new=closure_(RunNew.I(c+1))(Y)`, absent from the old pre-cut closure `Z_old); OR
- a complete old/upper dependent L+ pair appearing in the physical crossing relation of `Z_new` but missing from the full crossing relation of `Z_old`.

Now E38 literally identifies `Z_new` with `Z_bare=closure_(RunNew.I(c+1))(X∪O)`. Therefore that new terminal/full-pair witness already arises from the bare actual old+new ORIGINAL node seeds. It **cannot** be blamed on the bookkeeping convenience of preinserting `closure_I(X)`. This is the precise attribution needed in the geometric resolved-copy audit.

## Adversarial acceptance checklist

1. **Actual corrected seed definition:** new O is the image of real Kpt originals; do not revert to the mathematically false all-prefix initial seed model (a separate Lean counterexample shows all lower I1 levels then become interesting).
2. **Same horizon:** genuine selected-level monotonicity compares runs at ONE source-coordinate top, not old historical and newly enlarged different tops. The physical top-normalization/chronological cutoff still requires Track C's work.
3. **Literal same Kpt tree:** old X and new O must be literal admissible Kpt nodes in one normalized dependent L+ source. Merely matching ordinary L ages cannot imply seed inclusion.
4. **Old source levels ABOVE cut:** I⊆RunOld.I(c+1) must be proved, or deduced from I⊆RunOld.I0 plus c<q for q∈I. Dropping this is false in general.
5. **No no-I2 assumption:** a physical I2 cut may have multiple old→upper L+ pairs; comparing actual sets preserves all of them, not a fabricated single-valued F.target.
6. **No B3 converse:** I3 non-skippability is the actual Kpt monoid condition, not merely failed/passed corrected B3; literal closure equality preserves it directly.
7. **Parameter closure not distributive:** absorption requires least meet-and-parameter-closed supersets, not false generic union distributivity.
8. **E fake predecessor bits:** the source is literally the same Kpt node set; all complete assigned upper/old records and auxiliary negative/E bits survive.
9. **Finite physical avoidance:** hAvoid for the NEW finite H+ model remains an actual assumption in the physical specialization. This is *not* an automatic Henson extension witness.
10. **Different selected roots:** the theorem allows genuinely added original Kpt roots in O and new interesting cuts. It does not prove these cuts are exactly the prescribed macrodiary events.
11. **No source orbit from event equality:** two equal local pre-cut source descriptions do not identify different selected vertex labels across distinct embeddings or prove a common outgoing monoid inverse source.
12. **Cut-dependent canonical Y:** E40's canonical Y_c changes with c; do not silently claim one global corrected Y yields this identity simultaneously at EVERY cut without the corresponding old-higher levels property.
13. **No uniform BRD bound:** finite numerical source and exact closure identities alone do not provide an ambient-independent finite labelled envelope carrier.
14. **No silent manuscript green:** current full labelled orbit and upper BRD markers remain PENDING; Track G owns central imports and validation marks.

**Lean gate:** new independent `Kk/NewRootMonotoneAbsorptionBridge.lean` atop C #192, plus isolated explicit build and exact named standard-only transitive axiom audit, and independent full repository build. Both still require exact-head CI before certification.


## E42. No spurious LOWER interesting levels from preinserting old selected closure

The E38 source identity at one actual pre-cut also yields a useful **run-level** stability theorem below a boundary cut, provided the two relevant runs have already agreed above that boundary.

Fix ONE genuine (S,M)-tree, original seeds X and truly new seeds O. Define
`Y_bare = X∪O` and `Y_full = closure_I X ∪ O`.
Let `RunBare` and `RunFull` be two genuine AlgorithmRuns on these respective seed sets with the SAME top.

Fix a boundary `c<top`. Assume:
1. `I⊆RunBare.I0`: every old parameter-generating selected level is genuinely selected by the bare run;
2. `∀q∈I, c<q`: each such generating level lies STRICTLY above the boundary;
3. `RunBare.I(c+1)=RunFull.I(c+1)`: the two runs have ALREADY agreed on the higher selected levels at the boundary.

**Conclusion:** `∀i≤c, RunBare.I i=RunFull.I i`.

**Proof by descending induction over i=c,...,0.** The upper-level equality is hypothesis (3). If the sets agree at i+1, the run-tail identity gives `I⊆RunBare.I(i+1)` because i≤c and each inherited q∈I satisfies c<q. Track C's proved closure absorption at J=`RunBare.I(i+1)` says

`closure_J(Y_full)=closure_J(Y_bare)`.

Using `RunBare.I(i+1)=RunFull.I(i+1)`, these are EXACTLY the genuine pre-cut source closures of the two actual runs at i, including all meet/parameter Kpt nodes and their successor data. Therefore their ACTUAL `IsInterestingAt` decisions are literally equal, even at true I2 forks and regardless of corrected B3. If interesting, both choose `insert i` by their real `interesting_step` fields; otherwise both retain the next level set by their real `noninteresting_step` fields. The induction closes.

This is strictly stronger than E38's one-cut data comparison: **preinserting the old closure cannot introduce extra selected levels BELOW c once the higher-level run choices have aligned and all generating levels I are above c**. It is NOT a proof that their higher choices align: such alignment remains a geometric resolved-diary obligation.

### E43. Derive bare-run selection of I from an ACTUAL old run

Often `I⊆RunBare.I0` is not an independent checked fact. Suppose there is a third actual same-top run `RunOld` on X and `I⊆RunOld.I0`. Literal seed inclusion X⊆X∪O and Track E's verified actual run seed-monotonicity give `RunOld.I0⊆RunBare.I0`. Hence E42 applies automatically without an externally assumed retention certificate for RunBare.

Thus there is a three-run interface: `RunOld` on X, `RunBare` on X∪O, and `RunFull` on closure_I X∪O; if I was genuinely selected by RunOld, is above c, and Bare/Full agree at c+1, their **ENTIRE lower selected-level skeletons coincide**. The monoid shape maps may still differ. Neither the terminal-node identity/multiplicity nor common outgoing labelled inverse source follows from selected-level agreement.

### Hostile limits

1. Dropping the higher-run boundary equality is not justified: preinserted old closure may influence decisions AT/ABOVE generating levels I before a comparison below c begins.
2. Dropping the strict `c<q` condition allows `q∈I` to be absent from both pre-cut selected level sets, and inherited-closure pre-seeding may alter the closure.
3. Selected level-set agreement DOES NOT imply equality of the selected/per-parameter labels or their complete monoid inverse-source pullbacks.
4. Exact source equality at a step uses real meet-and-parameter closure absorption, not a false distributivity or a selected graph-age shadow.
5. There is no no-(I2) or (B3) assumption: genuine semantic `IsInterestingAt` is compared by literal equality of full Kpt sources.
6. The three runs MUST share the same source-level top and the same normalized Kpt tree; historic old/new numerical top/generation alignment remains to be proved separately.
7. The boundary `c+1` may itself be an interesting level selected differently for distinct actual resolved occurrences. The theorem is a conditional *propagation* result, not an automatic global diary theorem.
8. This still does not give a finite uniform parameter carrier or a single common fully labelled monoid inverse-source orbit.

Lean target: a generic two-run lower-tail absorption theorem and a three-run corollary which discharges bare-run inherited-level retention by genuine seed-growth monotonicity. Both to receive exact-head compilation and named standard-only transitive-axiom checks.
