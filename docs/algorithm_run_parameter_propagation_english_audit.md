# Actual AlgorithmRun propagation through previously generated Kpt parameters

## Status and purpose

This English proof and adversarial audit are written before the proposed
Lean implementation. They extend the genuine S3 parameter mechanism in
`Kk/B3GadgetClosureParameter.lean` from an original seed to a genuine
ambient original whose Kpt node is already in the full closure.

The intended new module is `Kk/AlgorithmRunParameterPropagation.lean`.
The implementation must wait for an independent review of this note.
No new theorem is described here as kernel checked. The eventual validation
gate is a complete pinned `lake build` followed by exact named transitive
axiom reports allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The new run statement deliberately uses a source available *before* the
run processes the selected cut. This makes the statement usable for an
iterated dependency of genuine parameters without assuming the desired
parameter in the final closure.

## Fixed data and notation

Fix natural-number signature dimensions `db`, `du`, `dd`, a list
`family : List (NormalizedForbidden db du dd)`, and one actual finite
`EnumeratedPartialStructure db du dd`, denoted by `A`. Assume

```
hAvoid : forall bad, bad in family -> bad.Avoids A.L.
```

All nodes, parameters and closures below belong to the same admissible
Kpt successor tree for this fixed family. For `v : Fin A.size`, write

```
O(v) = A.kptOriginal family hAvoid v,
f(c) = A.freeLevel c,
S = admissibleKptSTree family,
C(I) = SMTree.Envelope.closure S I X,
```

where `X : Set (AdmissibleKptNode family)` is fixed. If `c` is initially
a natural number, `O(c)` is used only after deriving `c < A.size`.
The level of `O(v)` is exactly `f(v.val)`. The free level is the actual
one determined by the ambient auxiliary E column; it is not a separately
chosen threshold.

`C(I)` is the existing complete componentwise-meet-and-parameter closure,
not a selected-only projection, an original-pool approximation, or a new
definition of closure.

## Auxiliary fact: monotonicity in the selected levels

For any successor tree `S`, arbitrary seed set `X`, and sets of levels
`I` and `J`,

```
I subset J  implies  closure S I X subset closure S J X.
```

**Proof.** Put `Y = closure S J X`. The existing theorems
`subset_closure`, `closure_meetClosed`, and `closure_parameterClosed`
show that `Y` contains `X`, is componentwise meet closed, and is parameter
closed over `J`. The existing
`ParameterClosedOver.mono_levels` restricts this last property to `I`.
The existing `closure_minimal` therefore gives
`closure S I X subset Y`.

The direction is essential: adding allowed parameter levels can only
enlarge the closure. No source-set enlargement or replacement of `X`
occurs in this proof. The pinned dependency has the four listed closure
APIs and the restriction lemma; this argument introduces no new closure
axiom.

The proposed public helper name is `envelope_closure_mono_levels` in
namespace `Kk`, avoiding edits to the pinned successor-tree dependency.

## Theorem 1: a positive parameter of any closed genuine original is closed

Proposed name:

```
kpt_closure_contains_positive_parameter_of_original_mem
```

Assume `v : Fin A.size`, `c : Nat`, and

```
O(v) in C(I),
c in I,
c < f(v.val),
0 < f(c).
```

Then

```
exists hc : c < A.size,
  A.kptOriginal family hAvoid (Fin.mk c hc) in C(I).
```

This replaces only the seed-membership premise `O(v) in X` of
`kpt_closure_contains_positive_parameter_of_seed` by the weaker genuine
closure-membership premise `O(v) in C(I)`. The seed set `X` stays fixed.

### English proof

Let `a = O(v)`. Since `c < f(v.val) = level(a)`, the two actual ancestors
of `a` at levels `c` and `c+1` exist. They are comparable below `a`, and
their levels differ by one, so the first is covered by the second.
The S3 axiom of the *constructed* admissible Kpt S-tree supplies a real
successor representation of this cover, with parameter list `P` and
letter `sigma`.

Apply the already proved `admissibleKpt_crossing_parameter` to this
successor representation, using `a <= O(v)` by reflexivity. It supplies
both the actual carrier bound `c < A.size` and the exact parameter record

```
P.map Subtype.val =
  if f(c) = 0 then [] else [A.rawTypeAtFree c].
```

Because `f(c) > 0`, the right side is the displayed singleton. Hence
some member `q` of the actual list `P` has raw value
`A.rawTypeAtFree c`. By subtype extensionality, `q` equals the genuine
node `A.kptOriginal family hAvoid (Fin.mk c hc)`.

The existing `closure_parameterClosed` applies to `a in C(I)`, the
selected level `c in I`, the strict level inequality, and the actual S3
successor representation. It puts every member of `P`, and therefore
the required genuine original, in `C(I)`.

This is the same physical successor calculation as the seed theorem.
The only changed step is that membership of `a` in the closure is used
directly rather than obtained from seed inclusion. The contract retains
the original seed set `X` and introduces no abstract parameter oracle.

### Shorter compositional implementation of the same proof

The existing seed theorem already contains the complete S3 calculation,
so the implementation can reuse it rather than duplicate that argument.
Set `Y = C(I)` and invoke
`kpt_closure_contains_positive_parameter_of_seed` with the auxiliary seed
set `Y`. Its source-membership premise is exactly `O(v) in Y`. It yields
the genuine target original in `closure S I Y`.

Now apply `closure_minimal` with source and target both `Y`. The seed
inclusion is reflexivity, while `closure_meetClosed S I X` and
`closure_parameterClosed S I X` provide the two closure properties of
`Y`. Thus `closure S I Y subset Y`, and the genuine target is in the
original `C(I)`, as required. This proves the needed direction of
idempotence from existing APIs within the proof; it does not assume an
idempotence axiom or permanently enlarge the algorithm's seed set.

This compositional proof is the intended implementation: one invocation
of the existing physical S3 theorem and one invocation of minimality.

## Actual run bookkeeping

Let

```
R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X runHeight.
```

For each `s <= runHeight`, the existing theorem
`R.I_eq_final_tail_of_run s` states

```
R.I s = {q | q in R.I 0 and s <= q}.
```

Consequently, for `s <= t <= runHeight`,

```
R.I t subset R.I s,
C(R.I t) subset C(R.I s).
```

The second inclusion follows from the auxiliary monotonicity fact.
These are consequences of the actual run's branch decisions. They need
neither `OneLevelPullback` (E1), a bound on the levels of `X`, nor output-map
coverage.

The inequalities supplied to `I_eq_final_tail_of_run` must be non-strict:
the API asks for `s <= runHeight`. In particular, from
`c < runHeight` use `Nat.le_of_lt` for the cut `c`, and
`Nat.succ_le_iff.mpr` for the cut `c+1`; do not try to turn `<` into `<=`
by a `simpa` invocation.

## Theorem 2: the run propagates a genuine parameter into every lower stage

Proposed name:

```
algorithmRun_selected_positive_parameter_in_lower_closure
```

In addition to the fixed ambient and actual run, assume

```
v : Fin A.size,
c : Nat,
c < runHeight,
O(v) in C(R.I (c+1)),
c < f(v.val),
0 < f(c),
c in R.I c,
p : Nat,
p < c.
```

Then

```
exists hc : c < A.size,
  A.kptOriginal family hAvoid (Fin.mk c hc)
    in C(R.I (p+1)).
```

The ambient original `v` may itself be a previously forced parameter.
It need not be one of the original seeds in `X`. Its genuine node must
already be in the actual pre-cut closure `C(R.I(c+1))`.

### English proof

First, since `p < c < runHeight`, both `p+1` and `c+1` lie in the run's
stage interval. The final-tail identity gives

```
R.I (c+1) subset R.I (p+1).
```

Explicitly, any `q` in the left set is final-selected and satisfies
`c+1 <= q`; since `p+1 <= c+1`, it belongs to the right set. Closure
monotonicity therefore transports the assumed genuine source `O(v)`
from `C(R.I(c+1))` into `C(R.I(p+1))`.

Second, the identity at cut `c` turns `c in R.I c` into `c in R.I 0`.
Because `p+1 <= c`, the identity at `p+1` gives

```
c in R.I (p+1).
```

Apply Theorem 1 with `I = R.I(p+1)`, the transported membership of
`O(v)`, this selected-level membership, the actual strict free-cut
inequality, and the positivity of `f(c)`. Its conclusion is exactly the
claimed genuine Kpt original in the lower-stage closure.

Equivalently, one can first promote the source from stage `c+1` to
stage `c`, force `O(c)` there, and then use monotonicity to reach every
`p+1 <= c`. Both proofs use only the already recorded selection at `c`.
Neither tries to deduce that selection from the new parameter.

### Iterated use and its limit

Suppose a higher selected cut `d` has already forced `O(d)` into the
closure at stage `d`. If a lower cut `c` satisfies `c < f(d)`, then
`f(d) <= d` implies `c < d`, hence `c+1 <= d`. The descending-stage
inclusion places `O(d)` in `C(R.I(c+1))`. If the actual run selects `c`
and `f(c) > 0`, Theorem 2 applies with `v` equal to the genuine carrier
vertex at `d`. Thus a previously generated parameter can force its own
true positive parameter at a later point of the descending scan.

This explains the new capability without introducing a theorem asserting
that an arbitrary chain is selected. The strict inequality
`c < f(d) <= d` prevents a dependency cycle in the numerical addresses.
Any application to a concrete diary must still supply each real selected
cut and each actual crossing/free-level fact.

## Theorem 3: actual B3 failures force two successive selected microevents

Proposed name:

```
algorithmRun_selects_two_step_B3_parameter_propagation
```

This endpoint removes the selected-cut premise for a genuine two-step
application. Fix the same `A`, `family`, `hAvoid`, and run `R` as above.
Assume a genuine seed `O(v) in X`, natural numbers `c` and `m`, and

```
0 < c,
c < runHeight,
c < f(v.val),
0 < f(c),
0 < m,
m < c,
m < f(c).
```

The first obstruction is an actual failed single-upper common-socle age
test at `c` for the ambient seed original `v`:

```
not (CommonSocleAgeTest family
  (prescribedOrdinarySocle (A.partialTypeAt (c+1) v.val)) c
  (fun T => T = (A.partialTypeAt (c+1) v.val).lReduct)).
```

The second obstruction is an actual failed two-upper common-socle age
test at `m` for the ambient originals at `c` and `v`:

```
not (CommonSocleAgeTest family
  (prescribedOrdinarySocle (A.partialTypeAt (m+1) c)) m
  (fun T =>
    T = (A.partialTypeAt (m+1) c).lReduct or
    T = (A.partialTypeAt (m+1) v.val).lReduct)).
```

Then

```
c in R.I c and
m in R.I m and
exists hc : c < A.size,
  A.kptOriginal family hAvoid (Fin.mk c hc)
    in C(R.I (m+1)).
```

The assumptions contain neither selection conclusion and do not assume
the derived original at `c` is a seed. The age tests use the complete
literal ambient L reducts over their prescribed common socles. They are
the tests already accepted by the actual one-upper and two-upper run
theorems, not tests on the marked or selected-only shadow.

### English proof

Apply the existing
`algorithmRun_selects_actual_failed_single_upper_B3` to the actual seed
`O(v)` and the first failed age test. Its premises are precisely
`0<c`, `c<f(v.val)`, `c<runHeight`, and `O(v) in X`. It concludes
`c in R.I c` for the actual supplied run.

Seed inclusion gives `O(v) in C(R.I(c+1))`. Theorem 2, with `p=m` and
the selection just derived, then yields a carrier witness `hc:c<A.size`
and the genuine `O(Fin.mk c hc)` in `C(R.I(m+1))`.
The original seed `O(v)` is in this same closure by seed inclusion.

Both genuine original types cross the lower cut: `m<f(c)` is a premise,
and `m<c<f(v.val)` gives `m<f(v.val)`. Also,
`m<c<runHeight` gives `m<runHeight`. Apply the existing
`algorithmRun_selects_actual_failed_two_upper_B3` with the first original
`Fin.mk c hc`, the second original `v`, the two established memberships
in `C(R.I(m+1))`, and the second failed actual age test. It concludes
`m in R.I m`. Pair the two selection conclusions with the carrier and
closure witness already obtained.

The chronology is: a failed actual test forces the higher selection;
that selection forces a genuine parameter into a lower pre-cut closure;
the two genuine upper types and a separately supplied failed actual test
force the lower selection. No step assumes the selection it proves.
The exact age tests remain substantive hypotheses to be verified in a
given ambient example. The concrete K4 configuration `v=38`, `c=22`,
`m=10` is a previously proved instance of this pattern, not a new
unconditional result for arbitrary diaries.

### Additional adversarial checks for the two-step endpoint

- The one-upper test is evaluated at cut `c` for the actual seed `v`;
  the two-upper test is evaluated at `m` for actual originals `c,v`.
  Neither may be replaced by an existentially similar-looking shadow.
- Both tests retain the full original socle. The two-upper theorem
  obtains common-ambient boundary compatibility from `A`; no separate
  frozen future-future L edge or arbitrary auxiliary E on age witnesses
  is imposed.
- Lower-source membership is established in `C(R.I(m+1))`, the precise
  closure used by the lower interestingness decision. Membership only
  in the final closure would not suffice for the run theorem.
- The higher source's lower eligibility is derived from
  `m<c<f(v.val)`; the generated source's eligibility `m<f(c)` is an
  independent necessary premise. Positivity `f(c)>0` alone would not
  make it an upper type at every lower cut.
- The statement is deliberately uniform over all runs satisfying the
  displayed premises, but it does not construct such a run or prove
  its output is an envelope. No unmentioned E1 assumption is used.
- The final endpoint has no premise `c in R.I c` or `m in R.I m`.
  These must both be present as derived facts in the formal proof.
- The displayed positivity conditions `0<c` and `0<f(c)` follow from
  `0<m<c` and `m<f(c)`. The formal signature omits them as redundant
  and derives them before applying the parameter-forcing theorem.

## Adversarial audit before formalization

1. **No selection from an E bit.** Theorem 2 retains
   `c in R.I c` as a premise. Positivity of the incoming E column alone
   does not discharge it.
2. **No circular final-closure premise.** The source is required in
   `C(R.I(c+1))`, before cut `c` is processed, rather than merely in the
   final closure. The result does not assume membership of the target
   parameter in any closure.
3. **Correct stage direction.** During the downward scan, the selected
   sets and their closures grow. The proof uses
   `R.I(c+1) subset R.I(p+1)` for `p<c`, never the reverse inclusion.
4. **Selected cut excluded from the pre-cut stage.** For `c<runHeight`,
   the existing `I_mem_bounds` implies `c` is absent from `R.I(c+1)`.
   The new closure membership is licensed by passing to a stage that
   actually includes `c`.
5. **Actual source type required.** An arbitrary node of the closure
   cannot be substituted for `O(v)` without a separate representation
   argument. The theorem fixes the genuine ambient original and its
   complete type. It does not infer source representation from an
   unlabelled graph image.
6. **One ambient and one family.** The crossing parameter and both
   source and target originals use the same `A`, `family`, and avoidance
   certificate. A parameter built in a different ambient requires an
   additional type-transport theorem.
7. **Carrier bound is a conclusion.** The natural number `c` is not
   silently treated as a carrier vertex. The crossing theorem derives
   `c<A.size`; this also follows arithmetically from
   `c<f(v.val)<=v.val<A.size`.
8. **Strict crossing.** `c=f(v.val)` is excluded. At the top level there
   is no next ancestor along `O(v)`, so S3 cannot be invoked as in the
   proof.
9. **Positive target free level.** If `f(c)=0`, the exact canonical
   parameter list is empty. The stated forcing argument then gives no
   target member. Positivity is not optional.
10. **Run-height bound.** `c<runHeight` makes the pre-cut stage `c+1`
    meaningful within the recorded scan. Values of `R.I` outside the
    specified run interval carry no such conclusion.
11. **Lower-cut boundary.** `p<c` yields `p+1<=c`, so the selected cut
    is present in the target stage. Taking `p=c` would refer to the
    pre-cut stage and is not justified. At `c=0` there is no natural
    `p<c`; positivity also rules out `f(0)>0` since `f(0)<=0`.
12. **Actual parameters, not an abstract map.** The singleton parameter
    record is obtained from `admissibleKpt_crossing_parameter` for the
    S3 witness of the actual admissible successor.
13. **Full closure retained.** The same existing meet-and-parameter
    closure appears in every premise and conclusion. Selected-only
    graph-age preservation does not replace full closure membership.
14. **No unnecessary E1 or top seed.** The argument needs neither
    `OneLevelPullback`, a seed-height bound, a distinguished top seed,
    nor numerical-H generation arithmetic. These should not be added
    as hidden premises just to make the proof elaborate.
15. **No injectivity claim for Kpt originals.** Distinct carrier
    addresses may have equal raw Kpt types. Subtype extensionality
    identifies the required complete type, but does not prove different
    addresses produce different nodes or preserve multiplicities.
16. **Iteration has explicit obligations.** A previously forced
    parameter can be reused only after its membership in the appropriate
    pre-cut closure is established. A hypothetical dependency graph or
    a future selection is not enough.
17. **Theorem 2 does not force lower selection.** Its conclusion is membership
    at the stage used to test an earlier cut. It does not supply a B3
    continuation witness or show that the earlier cut itself is selected.
    Theorem 3 supplies two actual age-test failures and derives both
    selections from them.
18. **No global construction claim.** This does not establish the
    prescribed infinite diary's mixed-neighborhood admissibility,
    physical canonical cover-age effects, occurrence-independent full
    I1/I2/I3/B3 records, common labelled inverse-source orbit, or either
    unconditional big Ramsey bound.

## Review and implementation contract

The independent review should check the chronology of the premise
`O(v) in C(R.I(c+1))`, the direction of both monotonicity arguments,
the strict crossing/positive-parameter conditions, and the precise
non-strict bound required by the run-tail API. It should also check
that the generalization genuinely removes original-seed membership
without assuming the conclusion under a renamed interface.

After that review, implement the two stated Kpt closure theorems, the
two-step actual B3-selection corollary, and the closure-monotonicity
helper in the new module only. Reuse the existing actual S3 seed theorem
through closure minimality, together with the pinned run APIs; do not
change the definitions
of closure, the admissible Kpt successor, or AlgorithmRun. Register
all public endpoints in the repository's strict named axiom audit
when integrating the module. Report build and axiom evidence only
after the complete checks succeed.

## Concrete integration into the existing K4 endpoint

The existing `k4Gadget_algorithmRun_selects_cuts10_22` can use Theorem 3
with the same actual finite structure, forbidden family, seed at 38,
and cuts `c=22`, `m=10`. Its higher failed test is
`k4H_actual_cut22_singleUpper_B3_failure`; its lower failed test is
`k4H_actual_cut10_twoUpper_B3_failure`. The existing exact free level
`k4GadgetH_q2_freeLevel_eq_11` gives `10<freeLevel(22)`, and
`k4GadgetH_top_freeLevel_above22` gives `22<freeLevel(38)`.
The new theorem returns the two selections in order 22,10; swapping
the two components recovers the unchanged public conclusion 10,22.
This is a concrete use of the general propagation theorem with already
proved age-test witnesses, not a new assumption of either selection.
