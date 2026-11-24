# Exact finite retained Plan from ordinary resolved-Q invariants

24 November 2026. English proof before implementation of the combined theorem.

This note closes the case split for the actual finite descending algorithm.
Its proposed theorem has ordinary graph, role, and canonical reference-age
hypotheses. It does not assume off-plan noninterestingness, absence of I1/I2,
a chosen B3 verdict, actual final-level equality, or a final-stage pool
description. The conclusion concerns the enlarged family of all planned cap
ancestors, not the smaller TOP-only seed family.

## 1. Exact data and hypotheses

Fix numerical height `k` with `4 <= k+1`, a finite carrier bound `N`, a
Boolean graph `E : Nat -> Nat -> Bool`, and
`role : Nat -> ResolvedQBaseRole`. Write

```
p(b,g) = hPosition k b g = 2*(k+1)*b + 2*g,
K = normalizedGraphModel E,
A = finiteNumericH K k N,
family = hensonForbiddenFamily 4,
```

where the proof of `2 <= 4` in `family` is suppressed. Require the following
ordinary construction hypotheses.

1. `E` has no loops and no ordered four-clique. The graph is symmetric by the
   next hypothesis. These conditions imply avoidance of `family` by `K` via
   `hensonForbiddenFamily_avoids_iff`; avoidance by `A.L` then follows from
   `finiteNumericH_avoids_family`. Thus finite-H admissibility is derived,
   rather than an additional semantic assumption.

2. `ResolvedQChronologicalAxioms role E`: symmetry; dummy-base isolation;
   no edge from an earlier coded base to a later auxiliary base; no edge
   between different auxiliary blocks; and a constant retained flag on
   each auxiliary block.

3. Auxiliary blocks are intervals modulo dummies. Precisely, for
   `u < b < v`, if `role u = auxiliary block a` and
   `role v = auxiliary block a'`, then `role b = dummy` or
   `role b = auxiliary block a''` for some Boolean flag `a''`.
   Ordinary interval convexity without the dummy alternative is not used.

4. Selected coded bases are independent:
   `role i = coded true` and `role j = coded true` imply `E i j = false`.

5. The physical cap is an actual bounded real original:
   `cap : Fin N`, `cap.val = p(b_cap,g_cap)`, `g_cap <= k`, and
   `role b_cap = dummy`. Put `tau = A.freeLevel cap.val`. Neither positivity
   of `tau` nor a special generation of the cap is required for the decision
   theorem.

6. At every **unretained meaningful base** before the cap, actual selected
   columns have no split and their full canonical reference age is neutral.
   Here this phrase means exactly

   ```
   p(b,0) < tau
   and (role b = coded false
        or exists block, role b = auxiliary block false).
   ```

   For each such `b`, require `ResolvedQSelectedNoSplitAt role E b`: for
   selected coded bases `j,j' > b`, agreement of the entire ordinary old
   columns `E(q,j)=E(q,j')` for every `q<b` implies
   `E(b,j)=E(b,j')`.

   Also require a finite list `target : Fin d -> Nat` with these exact
   properties:

   - each `target t` is a selected coded base strictly greater than `b`;
   - every physical TOP `p(target t,k)` lies below `N`;
   - every selected coded base `j>b` occurs in the list;
   - as functions on **all** `IntegerGraphSupport d 4`,

     ```
     baseTopPrefixCanonicalAge E 4 d b target
       = baseTopPrefixCanonicalAge E 4 d (b+1) target.
     ```

   The last equality is calculated from all old ordinary bases in `range b`
   and `range (b+1)` and from the actual columns `q |-> E(q,target t)`.
   Assigned age labels, equality of singleton values alone, or equality only
   on distinct nonrepeated future labels are not substitutes. The target
   list may repeat names; its exhaustive coverage here includes all future
   selected coded bases, not just the ones already known to lie in a guessed
   actual stage. This finite coverage is realizable when the selected code
   set is finite and lies before the chosen finite cap, as in the intended
   application. No selected code beyond the finite list is silently ignored.

There is no reference-age hypothesis at dummy bases or selected coded
bases. Their omitted lower cuts have a zero eligible ordinary star for
separate chronological reasons.

## 2. Constructed Plan, seeds, and claimed conclusion

Use exactly `numericRetainedPlan K k N cap role`. Equivalently, let `Kept`
consist of those `v : Fin N` for which `v.val < tau` and there are bounded
canonical coordinates `v.val=p(b,g)`, `g<=k`, satisfying either

```
role b = coded true and g=k,
or role b = auxiliary block true for some block.
```

Then

```
Plan = {0,tau} union {v.val : v in Kept}
                 union {A.freeLevel v.val : v in Kept}.
```

Let `C=A.kptOriginal family hAvoid cap`, with the derived avoidance proof,
and let

```
X = plannedPrefixSeeds C Plan
  = {z : z <= C and level(z) in Plan}.
```

**Proposed exact theorem.** For every genuine
`Run : AlgorithmRun (normalizedKptSMTree family) X tau`,

```
Run.I 0 = Plan,
Run.I i = {q : q in Plan and i <= q}             for every i <= tau,
IsEnvelope (Run.F 0).map X,
(Run.F 0).map.levelRange = {q : q in Plan or tau < q}.
```

In particular the existing canonical algorithm supplies such a run and
the stated envelope. No arbitrary source is chosen instead of its actual
output. The E1 input of the general envelope theorem is discharged by
`normalizedKpt_oneLevelPullback_for_envelopes family`.

These conclusions deliberately do not identify the compressed ordered
ordinary socle with the retained chunk enumeration. That additional source
calculation also requires all intended retained generations to lie before
the cap and the actual level-map range lifts. The present theorem provides
the exact selected level range needed for that calculation.

## 3. Derive singleton neutrality from full reference-age neutrality

Fix an unretained meaningful base `b` as in hypothesis 6 and a future
selected base `j`. Exhaustive coverage supplies `t : Fin d` with
`target t=j`. Let `pi : Fin 1 -> Fin d` be the constant map with value `t`.

Apply `finiteOldColumnCanonical_reindex` to the old pool `range b`, this
map, the actual target columns, and the genuine one-sort singleton support.
The resulting left side is exactly
`resolvedQK4SingletonCapacity E b j`; the right side is the full target-list
canonical age evaluated on the image of that singleton support. Repeat at
`b+1`. Evaluation of the full age equality on that same image gives

```
resolvedQK4SingletonCapacity E b j
  = resolvedQK4SingletonCapacity E (b+1) j.
```

This proves the full predicate `ResolvedQK4SingletonNeutralAt role E b`.
The pullback theorem allows arbitrary sort maps, so no injectivity of the
target list or unjustified identification of global class indices is
involved. If `d=0`, exhaustive coverage says there is no such `j`, so the
singleton predicate is vacuous.

The checked generation-zero theorem then derives any required old positive
neighbour from this actual singleton equality. No separate old-witness
premise is added. This step is specifically for the four-clique age; it does
not reinterpret a fixed-four singleton formula as an arbitrary forbidden
clique size.

## 4. Derived setup at an arbitrary omitted cut

Fix `c<tau`, `c notin Plan`, and the true descending induction hypothesis

```
Run.I(c+1) subset Plan.
```

All following structural facts are derived, not hypotheses of the proposed
main theorem.

- `0` and `tau` belong to Plan, every Plan coordinate is at most `tau`, and
  therefore `c>0` and `c<N`, using `tau<=cap.val<N`.
- Every planned level has its literal cap-ancestor seed, and there is no
  initial seed at `c`. The entire seed family is represented by the
  singleton physical root pool `{cap}`.
- The cap itself is a seed at height `tau`.
- The bounded dummy-cap role contract follows from the displayed cap
  address and bounded address injectivity.
- The exact bounded Plan role contract follows from
  `numericRetainedPlan_bounded_role_shape`: a Plan address with positive
  free level is a selected coded TOP or a retained auxiliary original.
- The Plan is closed under actual free levels. Applying the free-level
  operation twice to any finite original gives zero; hence the added free
  coordinates do not create new positive-free stage-original roles.
- If `c=p(b,g)` with `g<=k`, its omission implies
  `ResolvedQOmittedBase (role b)` by
  `numericRetainedPlan_omitted_real_role`. A retained auxiliary base cannot
  occur in this branch, since its real coordinate below the cap belongs
  to Kept.

All stage arguments now use exactly the full pool
`hStageOriginals K k N {cap} (Run.I(c+1))` and its actual closure-selected
predicate. The stage is never replaced by a proposed final diary pool.

## 5. Exhaustive cut cases

Every natural cut is odd or even. In the even case write `c=2*z`, divide
`z` by the positive number `k+1`, and set

```
b = z / (k+1),   g = z % (k+1).
```

Then `g<=k` and `c=p(b,g)`. Thus the following cases exhaust all off-plan
cuts; no numerical address is missing.

### A. Odd cuts

For `c=2*a+1`, apply
`henson_numericRetainedPlan_odd_run_skip` to this actual Run and the
descending hypothesis. It returns both `c notin Run.I 0` and
noninterestingness of the complete actual pre-cut closure.

The theorem uses free-level closure of Plan and of the actual cap root.
An omitted odd coordinate cannot be the free endpoint of a represented
stage original. Odd ordinary columns are zero, but the proof also retains
the actual incoming and outgoing E data. It is not an argument that zero
ordinary adjacency alone rules out a structural endpoint.

### B. TOP real cuts

If `c=p(b,k)`, use
`henson_actualRun_omitted_top_generation_skip` with the derived represented
seeds, no-seed condition, Plan shape, cap role, and omitted base role.

The full eligible TOP column equals the genuinely older generation-zero
column at `p(b,0)`: a positive TOP crossing forces a later TOP target, and a
positive generation-zero crossing is forced by the actual stage roles to
be a selected TOP. The TOP-to-TOP gate is true. Because `k>0`, the comparison
coordinate is strictly old, so full old-type equality forces full next-type
equality. This derives no-I1 and no-I2 on the whole actual stage.

If the cut were still selected, the actual nonstructural selected-cut
classifier would give a bounded real presentation with generation strictly
below `k`. Bounded injectivity contradicts its TOP presentation. The cited
theorem also gives the actual pre-cut noninterestingness. No inference from
the universal TOP B3 verdict to structural exclusion is made.

### C. Lower real cuts at dummy bases

Suppose `c=p(b,g)` with `g<k` and `role b=dummy`. Dummy isolation and the
exact eligible lower-cut decoder make the ordinary cut bit zero on every
eligible physical name of the actual stage. Apply
`henson_actualRun_isolated_dummy_lower_real_skip_of_no_seed`.
It derives no-I1, no-I2 and the actual B3 verdict, hence `c notin Run.I 0`.

### D. Lower real cuts at selected coding bases

Suppose `g<k` and `role b=coded true`. Chronological nonadjacency to later
retained auxiliary bases, dummy isolation and selected-code independence
make the whole eligible stage star zero. Apply
`henson_actualRun_selected_coded_lower_real_skip_of_no_seed` with the
derived actual Plan shape. Again this gives `c notin Run.I 0` without a
separate structural or B3 assumption.

### E. Remaining lower real cuts

The omitted-role classification, after excluding dummy and selected coded
bases, leaves exactly `coded false` or `auxiliary block false`. Moreover
`p(b,0)<=c<tau`, so hypothesis 6 applies to this precise base.

If `g=0`, apply
`resolvedQ_actualRun_zero_generation_no_full_I1_I2`. Its singleton premise
is derived in Section 3; its selected no-split and interval-modulo-dummies
premises are precisely the stated ordinary construction invariants.
Positivity of the tested coordinate comes from `0 in Plan` and omission.
The resulting exclusion covers all eligible physical stage originals,
including the cap and retained auxiliary names.

If `0<g<k`, apply
`resolvedQ_actualRun_positive_generation_no_full_I1_I2`, whose hypotheses
are already derived in Section 4. Neither singleton neutrality nor no-split
is needed in this positive-generation structural step.

For either lower-generation subcase, apply
`k4_resolvedQ_stage_B3_of_base_prefix_neutral` to the same full actual stage,
the actual closure-selected predicate, and the reference list from
hypothesis 6. The bounded chronological role theorem covers every eligible
positive physical stage name by a selected TOP on that list. The exact
failed full cut-star core only needs these positive names; zero cap or
auxiliary names may remain in the full source. Full reference-age neutrality
therefore gives the actual whole-stage chosen B3 verdict directly. No
marked-output-fibre premise is needed. For an empty list, exhaustive
coverage excludes positive eligible names; it does not assert that the
whole source is empty.

Now transfer this same actual pre-cut closure's full B3 verdict from stage
names to final names using
`finiteNumericH_run_stage_final_full_source_and_B3_eq` and the derived
no-I2. This transfer does not assert that the final pool equals Plan.
If the cut were selected, the actual no-I1/no-I2 I3 witness theorem would
produce a forbidden physical cut-star core and hence failure of precisely
that final chosen B3 test. This contradicts the transferred verdict.
This is the direct full-source tail of the existing proof in
`TrackDPreCutStageSource`, with its marked-source detour omitted.

### Convert every nonselection result to the required local conclusion

Cases C, D and E give `c notin Run.I 0`. If their actual pre-cut closure
were interesting at `c`, the actual `Run.interesting_step` would put `c`
in `Run.I c`. The unconditional final-tail identity
`Run.I c = {q : q in Run.I 0 and c<=q}` would then put `c` in `Run.I 0`,
a contradiction. This argument uses the run's true final levels and never
assumes they are Plan. Thus every case proves the required noninterestingness.

## 6. Complete descending induction and retain every planned level

Section 5 proves, for every genuine Run, the implication

```
c<tau, c notin Plan, Run.I(c+1) subset Plan
  => not IsInterestingAt H (closure tree (Run.I(c+1)) X) c.
```

This is an intermediate theorem proved from ordinary inputs, not a premise
of the combined exact-Plan theorem. At the top `Run.I tau={tau}` lies in
Plan. Descending induction preserves this containment at each planned cut
and skips each omitted cut by the derived implication. It gives
`Run.I 0 subset Plan`.

Conversely every planned level at most `tau` has its actual ancestor in
`X`. At a planned level below the top, that seed is an I1 witness in the
actual pre-cut closure. The level is therefore selected and lies in the
final set by the unconditional final-tail identity. The top is selected by
definition. Hence `Plan subset Run.I 0` as well.

The existing theorem `plannedPrefixSeeds_run_exact_plan` packages this
argument and, with the proved normalized Kpt E1 theorem, gives the exact
tail identities, whole-node envelope coverage and output level range
stated in Section 2. Taking the canonical AlgorithmRun yields the
existence version without any run hypothesis.

If `tau=0`, Kept is empty and Plan is `{0}`; there are no cuts in the
descending argument. The same conclusion holds. It gives no positive-size
G+ cap or selected terminal, and does not conflate a zero-level cap with
the positive-endpoint source-cardinality statement.

## 7. Nonvacuity with a genuinely positive omitted star

The ordinary hypotheses are jointly realizable without assuming the
conclusion. Take `k=4`, `N=89`, cap `p(8,4)=88`, and therefore
`tau=p(7,4)+1=79`. Give base 1 the retained auxiliary role
`auxiliary 0 true`, base 3 role `coded false`, bases 5 and 7 role
`coded true`, and every other base the dummy role. Let the ordinary graph
have exactly the symmetric edges between `{1,3}` and `{5,7}`.

This graph is loopless and four-clique-free, selected bases 5 and 7 are
independent, the chronological axioms hold, and the one-member auxiliary
block satisfies the interval condition. Every meaningful base has a dummy
immediately before it. Base 3 is the only unretained meaningful base before
the cap. Its future target list is `(5,7)`.

For every nonempty support on those two sorts, the common old pool at base
3 is `{1}`, and the pool after adding base 3 is `{1,3}`. Both pools have
directed clique capacity one because 1 and 3 are nonadjacent. Their raw
support bounds, and hence their complete canonical age functions, agree.
The two selected columns agree before base 3 and both receive bit true
there, so no-split holds as well. The omitted cut at `p(3,0)=30` has positive
eligible bits to both selected TOPs, so this example does not reduce the
remaining case to a zero ordinary star.

The concrete Plan is

```
{0,1,3,5,9,10,12,14,16,18,49,58,69,78,79}.
```

The theorem would derive exact selection for the actual planned-prefix
run from these data. This finite example does not assert universality or
an infinite resolved-Q realization.

## 8. What remains to instantiate for the manuscript

The finite descending algorithm has no further case gap under these exact
inputs. The manuscript application must still provide the actual graph and
roles and establish hypothesis 6 from the resolved event construction.
The proposed mechanism is concrete: identify actual class columns with the
fixed future selected-terminal list, use the arbitrary-sort canonical
pullback at each event (with distinct before/after class maps when needed),
and use monotonicity through the physical members of an omitted block to
pass from equal block endpoints to equality at every individual base.
The no-split assertion must likewise concern those actual selected columns.

These are ordinary finite construction duties; they are not a hidden
request to prove noninterestingness of the full Kpt source directly. A
proof that the infinite fair resolved-Q construction realizes the stipulated
events, the record-to-retained-member parser, and the common inverse-source
identification remain separate from this finite exact-Plan theorem.
