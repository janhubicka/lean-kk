# Track B: the exact continuation age at a selected nonfree pivot

## Status and scope

This English proof was written before its Lean implementation on 21 November
2026. It addresses the remaining ordinary-graph step identified after the
canonical sort transport and free-split results: determine the **whole joint
continuation age** at the same selected pivot, using all normalized clique
constraints, while retaining arbitrary protected passing columns. It does
not assume the desired continuation budget or assume that the requested
children survive.

The general conclusion is a finite, exact residual operation on an old canonical
age. The ordinary age must include the pivot's complete old type. When the
existing sorts do not include that type, one additional reference sort records
it. The full auxiliary E relation, parameter-closed Kpt source, event records,
corrected B3, and the prescribed infinite diary are separate obligations.

**The immediate formalization target is Section 6:** the manuscript's
controlled-coding inequalities themselves imply all actual pivot budgets,
and hence preserve the complete canonical survivor age. Its proof is direct
and does not depend on formalizing the more general residual operation first.

## 1. Physical data and residual vectors

Put n=ell-1, with ell>=2. Let P be a finite set of protected original
vertices in a fixed graph E. Let v be the **already selected** original pivot,
with v not in P, and assume the graph on P union {v} is K_ell-free.
All graph columns below are imposed in both directions. No vertex of P is
deleted or assigned a new old graph edge.

There are d old sorts and a complete old passing table c(p,t), for p in P.
An old sort s records the complete actual type of v:

    E(p,v) = E(v,p) = c(p,s),       p in P.

For every nonempty admissible old support S (|S|<=n), let

    B(S) = n - rho({p in P : c(p,t)=1 for all t in S}),
    F = G_B,

where rho is clique capacity and subtraction is truncated natural subtraction.
F is the full canonical age; it need not be positive at every sort. We use
the verified fact that a normalized integer vector respects B exactly when
it respects F. No assertion B=F is made.

Let pi map e new sorts to old sorts and let beta be their passing bits at v.
Repeated parents are allowed, and s may occur among the parents. The complete
new old table is

    C(p,u) = c(p,pi(u))          for p in P,
    C(v,u) = beta(u).

For a normalized new vector w, whose entries are natural numbers and whose
total mass is at most n, define two old-sort vectors:

    x(t) = sum of w(u) over pi(u)=t,

    y(t) = sum of w(u) over pi(u)=t and beta(u)=1
           + (1 if t=s, otherwise 0).

The first vector is automatically normalized: its total equals the total of
w. The second need not be normalized. Its total is

    1 + sum of w(u) over beta(u)=1.

Call w **residual-feasible** precisely when all three conditions hold:

1. x respects F on every admissible old support;
2. the total of y is at most n;
3. y respects F on every admissible old support.

The second condition is essential. If it fails, y is not an element of the
existing `IntegerCliqueWeights` type, and it cannot be silently truncated or
discarded. In Lean the bound must be established before forming that typed
vector, or the condition must be expressed using the untyped natural entries.

## 2. Exact vector theorem

Let B_plus be the actual raw bound from the complete new table C over
P union {v}. For every normalized new vector w,

    w respects B_plus  iff  w is residual-feasible.

This is a complete simultaneous criterion, including supports containing both
positive and zero children. It imposes no injectivity assumption on pi and
no separate all-support pivot-budget hypothesis.

### Proof by a literal finite clique

Take a finite set Q with w(u) vertices of each new sort u, disjoint from P
and v, and make Q a clique. These are abstract fresh vertices; they are not
being confused with previously selected original vertices. Join each q of
sort u to P according to c(p,pi(u)), and to v according to beta(u). Retain
the original graph on P union {v}. Let Q_plus consist of the vertices of Q
whose beta bit is one.

Because w is normalized, Q itself is K_ell-free. The old-plus-future
clique-capacity theorem applied to old set P union {v} says that its union
with Q is K_ell-free exactly when w respects B_plus. To pass between the
theorem's constraints on every subclique and the constraints on Q itself,
use that every subclique's multiplicities are coordinatewise at most w.

Every clique in P union {v} union Q either avoids v, or has all its future
vertices in Q_plus. Consequently this whole graph is K_ell-free if and only if
both of the following graphs are K_ell-free:

    P union Q,
    P union ({v} union Q_plus).

The forward direction is hereditary. For the reverse direction, a forbidden
clique avoiding v lies in the first graph, and a forbidden clique containing
v lies in the second graph. This also covers cliques with no future vertices.

In the first graph, Q is a clique with old-sort multiplicities x. The old
columns are exactly c, including when several children have the same parent.
The old-plus-future theorem over P therefore makes its freeness equivalent
to x respecting B, hence to x respecting F.

In the second graph, {v} union Q_plus is a **clique**, because the passing
bits are positive there and Q was a clique. Its old-sort multiplicities are
exactly y: the same selected v contributes one additional occurrence of s.
Its own K_ell-freeness is exactly total(y)<=n. Once this normalization is
known, the old-plus-future theorem over P makes freeness of the second graph
equivalent to y respecting B, hence to y respecting F.

Combining these equivalences proves the assertion. This proof uses the
existing canonicalization theorem on whole normalized vectors, not on
individual support bounds. In particular it does not assume that a decrement,
a linked-neighbour maximum, or restriction to positive children commutes
pointwise with canonicalization.

### Why the actual-pivot hypothesis matters

The freeness of P union {v} is necessary for this exact formulation. The zero
new vector always respects the nonnegative raw function B_plus. Its residual
test includes the old vector consisting of the pivot alone. If the actual
pivot were unsafe over P, that vector would fail. Thus one cannot remove the
old-plus-pivot freeness hypothesis merely because the displayed raw bound
uses truncated subtraction.

For a genuine Henson graph this hypothesis is inherited by the actual finite
prefix and introduces no additional construction obligation.

## 3. The full canonical age and one common finite realization

For every admissible new support U, define

    R_F,pi,beta,s(U) = max { sum of w(u) over u in U :
                            w is normalized and residual-feasible }.

The family is finite. It contains the zero vector: x=0, while y is the
single selected pivot, which is safe over P. The exact vector theorem gives
equality of the complete sets being maximized in the two descriptions, so

    G_(B_plus)(U) = R_F,pi,beta,s(U)

for **every** admissible support U. This proves the full joint continuation
age, not only its singleton survival or a value at one chosen support.
It remains valid when some new sorts have capacity zero.

There is also an explicit common finite future. For each residual-feasible
normalized vector w, take one fresh clique component Q_w with those labelled
multiplicities. Put no edges between different components. Give every
component the complete columns C to the same protected old graph
P union {v}. Each individual old-plus-component graph is K_ell-free by the
exact vector theorem. A clique with future vertices can meet at most one
component, so their union with the common old graph is K_ell-free.

Every residual-feasible vector is realized by its component, and every clique
inside this future is itself residual-feasible. For the latter statement,
deleting vertices decreases x and y coordinatewise (the pivot contribution
remains exactly one), so all inequalities and normalization remain true.
Thus this one finite graph realizes the entire new age without introducing
additional clique profiles.

When P union {v} is the complete actual protected prefix [0,H), the existing
relative Henson numerical-stage realization theorem applies at that same H.
It returns one embedding and one cutoff, fixes every original below H,
preserves every prescribed C column, and realizes all feasible profiles in
that common future. The selected pivot is fixed, not reselected. This is
precisely the existing physical realization with its raw feasibility family
now identified by the residual operation on F.

For a smaller arbitrary P, a claim about a complete physical prefix requires
first including every additional protected original and its passing column
in P; it is not legitimate to ignore active gap originals.

## 4. Arbitrary retained active columns require only one reference sort

Suppose the physical input is the complete prefix [0,H), v<H, arbitrary
background passing columns a(p,u), and new pivot bits beta(u). This is the
setting of `ProtectedActivePivotCapacity.lean`.

Set P=[0,H) minus {v}. Use e+1 old sorts: one reference copy of each of the
e future sorts, plus a reference sort s for the pivot. Define

    c(p,u) = a(p,u)           for a future-sort reference u,
    c(p,s) = E(p,v)           for the pivot reference s.

In the original symmetric graph this last column is also E(v,p). Let pi
send each future sort to its reference copy. The preceding theorem now
applies directly. It retains all actual nonpivot originals and their complete
possibly positive columns; none is replaced by a zero column.

Thus the desired full age is derived from the canonical age of this explicit
augmented old table and the residual test. The actual linked-neighbour
geometry is encoded in F through the pivot reference sort; no linked capacity
budget has to be independently postulated.

This augmentation must be stated honestly. Equality of an age on the future
sorts alone need not imply equality of the augmented age containing s. For
example, for ell=4 take two old adjacent vertices, both positive on the sole
future sort a. Its old canonical singleton age is one. If v is adjacent to
neither old vertex, a positive a child survives; if v is adjacent to both,
it does not, because the old edge and v already form a triangle. Both old
graphs with the pivot are K4-free. The additional pivot reference records
the difference that the unaugmented singleton age misses.

## 5. Consequence for comparing two physical occurrences

Consider two physical protected configurations, each with a genuine selected
pivot of reference sort s, the same labelled old sort domain and the same
parent map pi and passing pattern beta. They may have different old graphs,
different numbers of protected originals, and different raw clique bounds.
If their **complete canonical ages including the pivot type** agree, their
new complete canonical ages agree: both equal the same residual R_F,pi,beta,s.

This is a source-independent ordinary-graph transition once the stated old
canonical data are matched. It does not prove that unrefined diary data
already supply that match, nor does ordinary-age equality imply equality
of full dependent Kpt or auxiliary E source records.

## 6. Controlled coding derives every physical budget

This is the application to the controlled-coding definition in `kk.tex`.
It closes the ordinary-L controlled successor step without assuming its
conclusion as an all-support budget.

Retain the physical data of Section 1 and now assume the complete old
canonical age F is a genuine **positive** integer graph age. Let X be a
set of old sorts such that, for every admissible nonempty T contained in X,

    F(T) <= ell-2,

and, whenever T union {s} is also an admissible support,

    F(T union {s}) = F(T)+1.

The second hypothesis can be expressed without an ill-typed support as:
for admissible T and V, if T is contained in X and V's underlying set is
T union {s}, then F(V)=F(T)+1. The manuscript supplies this when X=E_s:
it has s not in X and states the equality for |T|<ell-1. Those forms agree
on the supports used below.

Let pi and beta be arbitrary, subject only to

    beta(u)=1 implies pi(u) belongs to X.

In particular, zero children may still have parent s. Then the new complete
canonical age is exactly

    G_(B_plus)(U) = F(pi[U])

on **every** admissible new support U. Thus arbitrary noninjective refinement
and deletion are permitted, all prescribed protected columns are retained,
and the same selected nonfree pivot realizes the required passing pattern.

### Proof: the missing large-support argument

Fix a new support U and put S=pi[U]. Canonicalization is below the old raw
bound, so

    rho(N(S)) + F(S) <= n,

where N(S) is its complete common-old-neighbour pool. Here F(S)>=1 makes
the conversion from truncated subtraction valid.

If beta has a zero on U, the pivot is absent from the new common pool. This
first inequality is the complete required raw budget for U.

Otherwise every parent in S belongs to X. We need to prove the second budget

    1 + rho(N(S union {s})) + F(S) <= n.

The tempting use of F(S union {s}) is invalid when |S|=n, since that union
can have n+1 elements. Instead, choose a nonempty Q contained in S such that

    |Q| < n,       F(Q)=F(S).

If |S|<n, take Q=S. If |S|=n, the controlled cap gives F(S)<=n-1<|S|.
The already proved small-support witness lemma, applied with both its supports
equal to S, supplies a proper nonempty Q contained in S with F(Q)=F(S).
Properness gives |Q|<n. Equivalently, take an F(S)-maximizing normalized
vector, restrict it to S, and retain its positive coordinates: their number
is at most F(S)<=n-1, and their F-value is still F(S).

Now Q union {s} is admissible. The controlled growth hypothesis and F<=B give

    rho(N(Q union {s})) + F(Q)+1 <= n.

Since Q is contained in S, the common-neighbour pool N(S union {s}) is
contained in N(Q union {s}). Clique capacity is monotone under pool inclusion.
Substituting F(Q)=F(S) proves the required second budget.

The exact pivot-pool formula now gives F(pi[U])<=B_plus(U) for every U,
including all mixed supports. The transported age U -> F(pi[U]) is a genuine
positive graph age by the verified arbitrary-sort pullback theorem. The
greatest-age-below-raw property therefore puts it below G_(B_plus).

Conversely, adding a pivot only enlarges a common-old-neighbour pool and
can only decrease its raw bound. Thus B_plus is pointwise below the old raw
bound pulled back under pi. Monotonicity of canonicalization and the verified
canonical sort-transport identity give

    G_(B_plus)(U) <= G_(B pulled back)(U) = F(pi[U]).

Both inequalities prove equality of the entire new age.

This argument uses only the controlled cap and growth conditions. The
additional singleton condition F({s})=1 and the final maximum identity in
the manuscript's definition are not needed for this preservation lemma.
They remain part of the controlled-coding definition and other diary tasks;
the lemma does not remove or reinterpret them.

### Complete physical stage

Apply the lemma with P=[0,H) minus {v} and with all actual old passing columns,
including nonzero active gaps. The exact new complete column is the protected
pivot column from `ProtectedActivePivotCapacity.lean`. The existing finite
numerical Henson realization theorem supplies one embedding and one cutoff,
fixes every original below H including v, and realizes the complete age just
proved equal to the pulled-back F. The embedding does not alter the original
graph or reselect the pivot.

For the literal controlled coding event, use the surviving sorts D minus {s}
as new sorts, take pi to be their inclusion, and set beta positive precisely
on E_s. The theorem gives exactly the restriction of F to those surviving
sorts. To identify this with the chronological event at the actual original
v, take H=v+1, so P is exactly [0,v). For a later protected cutoff H, the
theorem instead describes a finite continuation after accounting for every
nonpivot original below H, including those later than v. Identifying that
background age with an earlier diary state requires a separate history
invariant. Finite repeated-parent variants follow from the same statement.

### Focused hostile checks

* Checking only individual surviving children is insufficient; the proof above
  establishes the linked budget for every positive support and the ordinary
  budget for every support.
* The |S|=ell-1 boundary is handled by a proper saturating Q, not by an
  illegal evaluation of F on ell sorts. F(S)>0 ensures Q is nonempty.
* Duplicate parent fibres cannot enlarge the image cardinality, and no
  equality of child and parent support cardinalities is assumed.
* A positive parent may not be the pivot sort in the manuscript application;
  no exclusion is imposed on zero children. The abstract typed growth
  hypothesis already rules out any admissible positive support containing s.
* Full protected columns are used in N(S), so every relevant positive gap
  contributes to both the ordinary and linked budgets.
* The reverse inequality follows from raw monotonicity and canonical
  transport, not from an unproved claim that canonicalization itself creates
  exactly the intended age.
* The proof is finite ordinary-L mathematics. Full source labels and the
  infinite diary still need their own construction and audit.

## 7. Adversarial audit before Lean

The following are explicit checks on the proposed statement and proof.

1. **Same physical pivot.** The pivot in the residual vector is the existing
   v; left density does not replace it by a conveniently chosen new marker.
2. **Every protected original.** For a complete physical stage use
   P=[0,H) minus {v}. Positive selected, coding, reserved, and gap columns are
   all part of c; they cannot be reset by this argument.
3. **Actual-pivot safety.** P union {v} must be K_ell-free. Without this,
   the zero-vector test exposes a counterexample to the claimed equivalence.
4. **Both edge directions.** The chosen old sort s must describe the actual
   pivot in both directions. In the Henson application E is symmetric. A
   one-direction type is insufficient for the cited old-plus-future theorem.
5. **Multiplicity, not image cardinality.** x sums all child multiplicities
   in a parent fibre. If s is already a parent, y(s) includes its positive
   child multiplicity plus one, with no deduplication of the pivot.
6. **Total normalization is a separate condition.** y may have mass ell
   even when w has mass ell-1. Reject that vector before treating y as an
   `IntegerCliqueWeights` value. Support inequalities alone must not hide
   this condition, especially when the support of y has size ell.
7. **No oversized support coercion.** The proof never forms an old
   admissible support by adjoining s to an arbitrary child support. y is
   normalized first; only its ordinary admissible-support constraints are used.
8. **All joint support inequalities.** Both x and y must respect F on every
   admissible support. Separate singleton or pair tests do not replace this.
   The existing K4 pair obstruction is therefore not bypassed.
9. **Mixed children.** The whole future clique uses x, but only its positive
   part occurs with v and uses y. Applying the pivot condition to all of w
   would falsely exclude legitimate mixed cliques.
10. **Empty positive part.** Then y is the pivot alone. Its feasibility
    follows from actual-pivot safety, even when w has positive zero-child mass.
11. **Zero children.** F and R may vanish on some supports. The proof uses
    equality of feasible vector sets, which requires no positivity hypothesis.
12. **ell=2.** Here n=1; any positive child occurrence makes y have mass at
    least two and is rejected. Zero children obey the old pulled-back age.
    This is the correct behaviour in a K2-free graph.
13. **No positive bits.** Then y is always the safe pivot alone and the
    residual condition reduces to feasibility of x. This recovers ordinary
    canonical pullback under pi.
14. **No free-pivot substitution.** The argument uses the complete type s.
    The special empty-neighbour free-marker formula is not used in the proof.
15. **Abstract clones.** Q_w consists of fresh vertices. An old witness whose
    original index is already protected is not claimed to be outside the old
    prefix merely because its multiplicity vector is reused.
16. **One simultaneous future.** The disjoint union of all feasible clique
    components shares the same actual protected old graph and pivot. Its
    relative realization uses one embedding and one numerical cutoff.
17. **No raw-equality shortcut.** The proof uses canonical preservation of
    whole feasible vectors. It does not identify raw and canonical values.
18. **Adequate old data.** An appended pivot reference sort is additional
    canonical information when no old sort already describes v. The K4
    edge example above disproves using the unaugmented age alone.
19. **Finite scope.** Matching this ordinary residual is not a proof of
    I1/I2/I3, corrected B3, a common labelled inverse-source orbit, or an
    infinite prescribed diary schedule.

## Implementation obligations

First formalize Section 6: derive the missing linked budgets from the
controlled inequalities, prove equality of the complete canonical ages, and
instantiate the existing same-pivot finite Henson realization. Its hypotheses
must not already assert the desired joint budget. The more general residual
operation in Sections 1--5 is a separately justified extension and need not
delay that controlled-coding result. The arbitrary-active-column specialization
must use the complete prefix and the actual pivot type. A central build and
named standard-only axiom audit are needed before assigning Lean validation
marks. Until those run, this note is an English proof and audit record only.
