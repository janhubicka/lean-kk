# Concrete finite retained Plan and odd-cut closure

24 November 2026. English proof before implementation of
`Kk/NumericRetainedPlan.lean`. This follows the independently reviewed
planned-prefix seed construction and uses the unchanged numerical-H
constructor at successor pin `a74c10761303a18649053f2af3a1a1697f032e13`.

## Definition: finite retained original addresses and Plan

Fix the actual finite numerical-H structure A=finiteNumericH(K,k,N),
a genuine cap index cap:Fin N, and a role assignment
role:Nat->ResolvedQBaseRole. Put tau=A.freeLevel(cap.val).

Define Kept as the finite subset of Fin N consisting of exactly those v
such that v.val<tau and there exist b,g with

    g<=k, v.val=hPosition(k,b,g), and either
      role(b)=coded(true) and g=k,
    or role(b)=auxiliary(block,true) for some block.

This definition retains every generation of each retained auxiliary
base below the cap, and only TOP for a selected coded base. The strict
bound below tau is in the definition, so infinitely many future role
flags do not make this finite plan unbounded.

Define the concrete finite set

    Plan = {0,tau} union {v.val:v in Kept}
                   union {A.freeLevel(v.val):v in Kept}.

Neither a free-cut closure premise nor a Plan-shape premise is part of
this definition. The following arguments derive both from the real
finite-H constructor. The singleton physical root is still cap.

## 1. Applying the free-level operation twice gives zero

For any finite-H original address v<N, A.freeLevel(v)<=v<N.
The canonical free level of address zero is zero, since it is <=0.

Every odd target 2a+1 has an empty incoming auxiliary E column, by
`exactHEBool_odd_target_false` and `finiteNumericHE_true_iff`. Its
canonical free level is therefore zero: otherwise E(0,2a+1) would be
true by `E_iff_freeLevel`.

If A.freeLevel(v)=0, applying freeLevel once more gives zero. If it is
positive, `finiteNumericH_positive_freeLevel_odd` says it is an odd
number, and the preceding odd-target calculation gives zero. Thus

    A.freeLevel(A.freeLevel(v))=0.

All coordinates here are in the finite carrier. In particular, this
is not a claim about an unspecified out-of-carrier free-level table.
The argument also permits k=0; no positive-height premise is needed.

## 2. Plan is finite, bounded, and closed under actual free cuts

It is finite by its explicit Finset construction. It contains 0 and
tau. Every kept real coordinate is strictly below tau, and its free
level is at most that coordinate. Hence every member of Plan is at
most tau. Since tau<=cap.val<N, all planned coordinates are in the
finite carrier.

Let v:Fin N have v.val in Plan. There are four possibilities.

* v.val=0: its free level is 0, which is in Plan.
* v.val=tau=A.freeLevel(cap.val): its free level is 0 by Section 1.
* v belongs to Kept: its free level is explicitly included in Plan.
* v.val=A.freeLevel(w.val) for w in Kept: its free level is 0 by
  Section 1.

Therefore Plan is closed under the actual freeLevel operation on
every original address in Plan, without even requiring the free level
to be positive. In particular this supplies the positive-free-cut
closure premise of `henson_actualRun_odd_omitted_of_closed_plan`.
The root free cut is tau, explicitly in Plan, so the singleton-root
closure premise is also discharged.

## 3. The repaired bounded Plan-role contract is derived

Suppose v:Fin N belongs to Plan and A.freeLevel(v.val)>0. Sections 1
and 2 exclude the anchor, cap-end, and added-free-cut summands: all
these original addresses themselves have free level zero. Hence
v.val comes from a kept real original w. Since v.val=w.val and both
are Fin N, v=w.

The Kept definition supplies a canonical address hPosition(k,b,g),
g<=k, with the required retained role and generation. If the caller
also presents v.val=hPosition(k,j,m), with m<=k, the checked theorem
`hPosition_injective_bounded` gives j=b and m=g. Thus

    role(j)=coded(true) and m=k,
      or role(j)=auxiliary(block,true) for some block.

This is precisely the repaired Plan-shape contract used by the
whole-stage source classification. No unbounded generation decoder
is introduced. No assumption role(0)=dummy is required here: the
positive-free-level guard already excludes coordinate zero.

## 4. Omitted real cuts have an omitted base role

Suppose c=hPosition(k,b,g)<tau, g<=k, and c is not in Plan. The bound
tau<N makes c an actual finite original address. If role(b) is a
retained auxiliary role, c belongs to Kept and hence Plan, a
contradiction. Therefore the role is dummy, coded(selected) for one
of the two Boolean flags, or an unretained auxiliary role. This is
exactly `ResolvedQOmittedBase(role(b))`.

In the selected-coded case, g=k is likewise impossible at an omitted
cut: its TOP address would be kept. The omitted-base conclusion itself
allows both coded flags, as required by the existing stage theorem.

For the singleton cap root, a genuine bounded canonical presentation
cap.val=hPosition(k,c,r), r<=k, with role(c)=dummy, also derives every
bounded root-role presentation by `hPosition_injective_bounded`.
The assumption that the chosen cap's actual base is dummy remains a
concrete input; it is not inferred from its zero ordinary column.

## 5. Actual omitted odd cuts are skipped for the enlarged seed family

Take X=plannedPrefixSeeds(cap's actual Kpt original,Plan), and an
actual AlgorithmRun on X at top=tau. Let c=2a+1<tau be omitted from
Plan, and assume the true descending inclusion R.I(c+1) subset Plan.
Under the existing Henson simplicity, symmetry, clique-free and
height hypotheses, the established odd-cut theorem applies as follows.

1. X is represented by the singleton physical root {cap}, by the
   planned-prefix seed adapter.
2. The cap itself belongs to X because tau belongs to Plan, giving
   an actual top seed.
3. The cut bound c<N follows from c<tau<=cap.val<N.
4. Root free-cut retention and Plan free-cut closure are conclusions
   of Section 2, not new premises.
5. Since c is outside Plan, there is no initial X seed ending at c.
6. The established physical odd-cut result supplies the complete
   no-I1/no-I2/no-I3 exclusion; it covers the full parameter closure.

Consequently c is absent from the actual final selected-level set.
This is a genuine one-cut application for the enlarged X, not an
unchanged invocation of the smaller top-generation-seed corollary.
The descending inclusion is still the induction hypothesis; this
theorem does not assume final-level equality with Plan.

## Adversarial scope checks

* The cap is a member of Fin N, so N>0 and every used free cut is inside
  the finite structure. No out-of-carrier free cut enters the plan.
* Kept uses the strict cap-end bound; retaining a meaningful role after
  the cap cannot accidentally add a later generation to this Plan.
* A retained auxiliary base includes all its generations that lie
  below the cap. A later argument claiming all generations are below
  the cap must prove that physical bound; the definition does not.
* Added free-cut coordinates are not ordinary-L isolated from every
  aspect of L+: their outgoing E entries may be positive. The proof
  only uses their empty incoming E columns and zero free levels.
* Coordinate zero is included even when no generation-zero original
  is kept. Its zero free level prevents an unintended stage original.
* The canonical bound m<=k remains explicit whenever hPosition is
  decoded. This avoids the earlier cross-base alias defect.
* The auxiliary retained flag must agree across members for the
  separate chronological edge lemmas, but Plan closure and shape do
  not need that unrelated edge axiom.
* This construction does not establish resolved-Q age neutrality,
  selected no-split, or corrected B3 at the remaining real cuts.
* Odd skipping is proved on the actual enlarged-seed run and actual
  higher-stage set. Nothing is inferred from a selected-age shadow.
* The finite retained tables' record dependence remains a separate
  construction theorem; Plan finiteness alone does not identify a
  common source across two diary occurrences.
