# Track B: controlled pre-ages before choosing a numerical pivot

## Status and exact scope

This English argument and independent adversarial audit were committed before
the corresponding Lean implementation at
[`69dafd21dfbeb2923d204a106d860e2c2910657a`](https://github.com/janhubicka/lean-kk/commit/69dafd21dfbeb2923d204a106d860e2c2910657a).
The stronger direct raw-capacity argument in Section 5 was also committed first,
at [`528c4f14f06071f087e550db323c5ce88cb3b85b`](https://github.com/janhubicka/lean-kk/commit/528c4f14f06071f087e550db323c5ce88cb3b85b).
They concern the manuscript's `Lem:Kk_Controlled_PreAge` and finite ordinary
graph-age preparation of a controlled coding event.

**Verification status: complete hosted gate passed.**
[Run 44920690130](https://github.com/janhubicka/lean-kk/actions/runs/44920690130),
[job 136895846770](https://github.com/janhubicka/lean-kk/actions/runs/44920690130/job/136895846770),
checked source `69983310fc1acd65a31c9d99cbc6f56ffb796532` through the actual merge
`147bd10c6372839c77bc0df52ffeb0583dea3b90`. The 9,738-job build, parser
self-test and **990 exact named transitive-axiom reports** passed, permitting
only `propext`, `Classical.choice`, and `Quot.sound`; seven reports are
axiom-free. The source registry has 989 names, and the tested merge adds one
independent main endpoint. All source names remain in order, and all Track B
proof files and pinned dependencies are identical. Source and tested trees
are different; their exact comparison and all reports appear in the
[evidence record](audits/2026-11-21-track-b-controlled-preage.json).

`ControlledPreAge` contains 11 registered endpoints for the genuine constructor, controlled
identities, uniqueness, minimality, and canonical relative consistency;
the module also passed its direct local Lean check. `ProspectiveControlledPreAge`
adds six endpoints deriving the literal abstract-event formula, legality,
cap and lower bound. `PhysicalProspectiveControlledCoding` adds two final
interfaces combining the computed `R` and `C` with actual finite preparation
and coding at a later numerical pivot. Together with the nine normalization
and late-pivot endpoints described in the companion note, these are **28 new
endpoints** beyond the previous 961-report checkpoint. No completed local
full-project gate is claimed.

The final interfaces take no desired `C ≤ P`, prepared-age equality, pointed
budget, or previously chosen numerical pivot as inputs. The general
residual-vector operation in Sections 1–5 of the earlier residual note remains
English-only; the present formal route uses the direct raw-capacity argument
and the verified controlled-coding theorem. The exact residual-vector
calculation in Section 3 here is an English explanation, not a separately
registered general residual theorem.

The same-domain representation of `R` causes no hidden deletion assumption.
`prospectivePivotRaw_eq_abstract_extension` identifies its raw table with the
literal abstract pivot's complete columns. The existing
`finiteOldColumnCanonical_reindex` theorem then identifies `R(pi[U])` with
the canonical age of those columns on the reduced survivor sorts. This uses
physical complete-column reindexing and its derived support monotonicity;
it does not assert deletion locality for arbitrary raw functions.

For a given actual chronological ordinary-graph coding event with the complete
bilateral old pivot column, `protectedPivotRaw_eq_actual` and
`oldSupportCommonNeighbourPool_mutual_pivot` rewrite its next-prefix raw age
to the same prospective formula. Under the same positivity hypotheses on every
survivor support and the old pivot singleton, the lower bound `C ≤ P` therefore
also applies to such a given event, independently of how that pivot was selected.
This is a composition of the checked raw identities and the prospective
theorem, not a separate general residual-vector theorem.

These finite results do not prove a prescribed chronological saturated-cover
schedule, full parameter-closed `Kpt`/auxiliary E history, (I1)–(I3) or corrected
(B3) transport, a common labelled inverse-source orbit, or the infinite
resolved-copy construction. Identification of the manuscript's abstract
enumeration/density formulation with the explicit Boolean `OnePointLeftDense`
input also remains a separate adapter. See [the current validation entry](validation.md)
for the gate and finite-regression scope.

The key distinction is between an **abstract finite pivot extension**, used to
calculate a prospective post-age, and the **later numerical original**, chosen
only after the auxiliary blocks have been reserved. The former has a complete
old type but need not already have a numerical index. No previously committed
selected, reserved, or parameter original is moved or reselected.

Relevant existing sources are:

* `Kk/IntegerWitnessCanonical.lean`: normalized integer graph ages and their
  canonicalizer;
* `Kk/CoverSubfrontIntermediateLift.lean`: the same-domain
  `IsSubfrontIntegerGraphAge` interface;
* `Kk/RawWitnessNormalization.lean`: equivalence with raw integer witnesses;
* `Kk/IntegerAgeSmallFunction.lean`: support monotonicity;
* `Kk/IntegerAgeUniversalProperties.lean`: equality of complete raw and
  canonical feasible-vector families;
* `Kk/ControlledPivotBudget.lean` and `Kk/PhysicalControlledCoding.lean`: the
  already verified coding step once the controlled pre-age is present;
* `docs/track_b_nonfree_pivot_residual_english_audit_20261121.md`, Sections 1--5:
  the exact residual-vector theorem, still an English theorem;
* `docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`:
  the separate finite target-normalization and late-pivot construction.

## 1. Domain-safe formulation

Put `n = ell - 1`, with `ell >= 2`. Let `D` be a finite set of sorts, let
`j in D`, and put `E = D \ {j}`. Let `X` be a subset of `E`. Supports are
nonempty finite sets of at most `n` sorts.

Let `R` be a genuine positive integer graph age on `E`. In the existing
same-domain Lean representation this means

    IsSubfrontIntegerGraphAge d ell (Finset.univ.erase j) R.

Here `R` may be represented by a total function on ambient admissible supports,
but its values outside `E` are irrelevant. All evaluations below are on subsets
of `E`. Extend it to the empty set by `Rbar(empty) = 0`; otherwise `Rbar(A)=R(A)`.
Only sets of cardinality at most `n` are evaluated.

Assume the **all-support positive cap**

    R(A) <= n - 1

for every nonempty admissible `A subset X`. This includes supports of size `n`.
Define, for every admissible ambient support `T`,

    C(T) = R(T)                                      if j notin T,
    C(T) = max(Rbar(T \ {j}),
               1 + Rbar((T \ {j}) intersect X))      if j in T.

Every argument of `Rbar` is a subset of `E`. In the second line it has size at
most `n-1`, since one element of `T` is `j`. Empty arguments are never passed
to the nonempty-support function `R` itself.

For any `A subset E` of size at most `n`, there is an `R`-feasible witness
supported on `A` with total weight `Rbar(A)`: use the zero vector for `A=empty`;
otherwise take a consistency witness for `R(A)` and zero every coordinate
outside `A`. Zeroing decreases every tested sum and preserves its sum on `A`.
The same witness argument proves monotonicity of `Rbar` on this domain.

## 2. The constructor is a genuine graph age

First, `1 <= C(T) <= n`. If `j notin T`, this is the age bound for `R(T)`.
If `j in T`, the first maximum term is at most `n`. The second is at most `n`
by the positive cap when its argument is nonempty, and equals `1 <= n` when
that argument is empty. It is also at least one.

Fix `T`. We construct a supported consistency witness attaining `C(T)` and
check **every** ambient test support `V`.

### The term without the pivot

If `j notin T`, use a witness supported on `T`. If `j in T` and the first
maximum term is chosen, put `S=T\{j}` and use a witness supported on `S`.
Give `j` weight zero. At a test support not containing `j`, its sum is bounded
by `R(V)=C(V)`. At a test support containing `j`, its sum is bounded by
`Rbar(V\{j}) <= C(V)`. The empty intersection has sum zero. The total is
at most `n`, and the sum on `T` is the chosen first term. In a maximum tie,
either construction is permitted.

### The term containing the pivot

Suppose `j in T` and choose the second maximum term. Put
`A=(T\{j}) intersect X`. Take an `R`-feasible witness `w` supported on `A`
and give the pivot weight one. The resulting vector has total

    1 + Rbar(A) <= n.

For a test `V` not containing `j`, the sum is the old witness sum and is at
most `R(V)=C(V)`. For a test `V` containing `j`, support inside `X` gives

    sum_V = 1 + sum_{(V\{j}) intersect X} w
          <= 1 + Rbar((V\{j}) intersect X)
          <= C(V).

This checks arbitrary mixed supports, not merely supports contained in `T`
or `X`. The sum on `T` is exactly the chosen second term. Thus every `C(T)`
has a normalized consistency witness, so `C` is a genuine positive age.

The Lean proof may equivalently build these as raw `Fin d -> Fin ell`
witnesses first, then use `rawIntegerGraphAge_iff_normalized`. The bound on
the chosen total above explains why no normalization hypothesis is missing.

## 3. Controlled identities, uniqueness, and exact coding

The formula immediately gives

    C({j}) = 1,
    C(U) = R(U)                       for U subset E,
    C(U union {j}) = Rbar(U) + 1      for U subset X, |U| < n.

For `ell >= 3`, every pair `{j,x}` with `x in E` is in the support domain.
Positivity of `R({x})` then gives

    C({j,x}) = R({x}) + 1            if x in X,
    C({j,x}) = R({x})                if x notin X.

Consequently the passing set recovered by the manuscript's pair equality is
exactly `X`. The all-support positive cap transfers from `R` to `C` on `X`.

For the final controlled identity, use the zero extension on empty sets. If
`j notin T`, monotonicity gives `C(T intersect X) <= C(T)`. If `j in T`, put
`S=T\{j}` and `A=S intersect X`. Then

    C(T\{j}) = Rbar(S),
    C(T intersect (X union {j})) = 1 + Rbar(A),

so the desired maximum identity is precisely the defining formula for `C`.
This verifies all manuscript controlled axioms.

There is a useful uniqueness statement: if another controlled age `F` has
passing set `X` and restricts to `R` on `E`, then `F=C`. Indeed, for a support
containing `j`, the final controlled identity reduces it to `S=T\{j}` and
`A union {j}` with `A=S intersect X`. Since `|A|<n`, controlled growth gives
`F(A union {j})=Rbar(A)+1`; the singleton case supplies the same assertion
for `A=empty`. This recovers the displayed formula. Supports not containing
`j` already agree.

### Exact feasible vectors after coding

Let `w` be a normalized survivor vector on `E`. Let `x` be its zero extension
at `j`, and let `y` give `j` weight one, retain `w` on `X`, and give every
other coordinate weight zero. The abstract residual criterion for coding
is that `x` is `C`-feasible, `y` is normalized, and `y` is `C`-feasible.

If these conditions hold, testing `x` on supports in `E` shows that `w`
respects `R`. Conversely, suppose `w` respects `R`. The verification for `x`
is the first witness calculation above. Let `Q` be the positive-weight support
of `w` inside `X`. If nonempty, its cardinality is at most the total weight
of `w`, hence at most `n`, and

    sum_X w = sum_Q w <= R(Q) <= n-1.

If empty, that sum is zero. Thus `y` is normalized. For every test support,
the second witness calculation above proves `y` is `C`-feasible. Therefore
the residual feasible survivor vectors are **exactly** the `R`-feasible
vectors. Canonicalization recovers precisely `R`, since a genuine age is
a fixed point of the canonicalizer. This proves the ordinary graph-age
meaning of “coding j leaves precisely R.” The already verified physical
controlled-coding theorem supplies the same conclusion when `C` is the
complete actual pre-age of a physical pivot.

## 4. Exact lower-bound criterion: when is C below P?

Let `P` be any support-monotone nonnegative function on the ambient support
domain. Then `C <= P` is equivalent to these three explicit tests:

1. `R(U) <= P(U)` for every admissible `U subset E`;
2. `1 <= P({j})`;
3. `1+R(A) <= P(A union {j})` for every nonempty `A subset X` with `|A|<n`.

For a genuine age `P`, the second test is automatic. Necessity follows by
evaluating `C <= P` at the indicated supports. For sufficiency, there is
nothing to prove beyond test 1 when `j notin T`. If `j in T`, the first term
`Rbar(T\{j})` is bounded by `P(T)` using test 1 and monotonicity, or by zero
when its argument is empty. The second term is bounded using test 3 and
monotonicity, or using test 2 when its argument is empty. Taking the maximum
proves `C(T)<=P(T)`.

This is a genuine criterion, not an assumption of the desired conclusion.
In particular, survivor domination alone does not imply the pointed tests.

## 5. Noncircular prospective event over complete protected columns

Let `A` be a finite protected graph, with all selected, reserved, and parameter
originals that have already been committed included. Assume it is
`K_ell`-free. Supply a complete bilateral old table `c(a,t)` for `a in A`
and `t in D`. Let `B` be its raw common-neighbour clique bound and let
`P=G_B` be its full canonical age.

Add an **abstract** vertex `nu`, disjoint from `A`, with its adjacency to
each `a in A` exactly `c(a,j)`. Assume this finite one-point extension is
`K_ell`-free. This condition can instead be derived from `P({j})>=1` by
raw/canonical vector equivalence: the pivot-only vector must be feasible.
For survivor sort `x in E`, preserve its full column over `A` and assign its
bit at `nu` to be `1` exactly when `x in X`.

Let `Bplus` be the raw common-neighbour bound over `A union {nu}` on the
survivor sorts, and **define** `R=G_Bplus`. Assume positivity on every
computed survivor support, so this is a genuine graph age. This is the normal “all listed
sorts survive” qualification, not an assumption that `C<=P` or a desired
post-age is achieved.

The canonical function `P` is support-monotone even before positivity is
known: it is the maximum of a fixed family of nonnegative support-sum
functions, each of which is monotone. Thus Section 4 applies to this `P`.

Then the positive cap and `C(R,X)<=P` follow as conclusions.

For the cap, take any nonempty admissible `U subset X`. The vertex `nu`
belongs to the full common-neighbour pool for `U`, so its capacity is at
least one. Hence

    R(U) <= Bplus(U) <= n-1.

For survivor domination, take a maximizing `R`-feasible clique witness on
`U`, supported inside `U`. Raw/canonical vector equivalence realizes it as
an abstract clique `Q` whose prescribed gluing to `A union {nu}` is
`K_ell`-free. Deleting `nu` leaves a legal old-type clique over `A`, so its
zero extension at `j` is `P`-feasible. This gives `R(U)<=P(U)`.

For a nonempty positive support `U subset X` of size less than `n`, use the
same maximizing witness supported on `U`. All its vertices are adjacent
to `nu`, so `{nu} union Q` is a clique of old sorts supported on
`{j} union U`. Its size is `1+R(U)<=n` by the cap. Its gluing to the old
graph `A` is the same legal graph, hence it is `P`-feasible and gives

    1+R(U) <= P(U union {j}).

The empty positive support is handled by the legal pivot alone, which gives
`1<=P({j})`. Section 4 now proves `C(R,X)<=P`. Equivalently, one may use the
exact residual-vector theorem from the earlier English audit to replace
the finite clique argument by feasibility of the two vectors `x` and `y`.
Either proof uses the complete pivot column and all protected originals.

There is an even more direct route suitable for formalization: prove the
stronger pointwise statement `C<=B`, then use the canonicalizer's greatest-age
property. Write `N(T)` for the old common-neighbour pool. For `j in T`, put
`S=T\{j}` and `U=S intersect X`. The first term `Rbar(S)` is at most `B(T)`:
when `S` is nonempty, use `R(S)<=Bplus(S)<=B(S)<=B(T)`; otherwise it is zero.
When `U` is nonempty, adjoining `nu` to a maximal clique in `N(T)` gives a
clique in the new common-neighbour pool for `U`, because `U union {j}` is
contained in `T`. Therefore

    1 + rho(N(T)) <= rho(Nplus(U)).

The full abstract old-plus-pivot graph is `K_ell`-free, so the latter
capacity is at most `n`. Combining this with `R(U)<=n-rho(Nplus(U))` yields
`1+R(U)<=n-rho(N(T))=B(T)`. If `U` is empty, legality of the pivot alone
gives `rho(N({j}))<=n-1`; since `N(T) subset N({j})`, the second term one
is again at most `B(T)`. Supports not containing `j` use
`R(T)<=Bplus(T)<=B(T)`. Thus `C<=B`, and the genuine-age conclusion of
Section 2 gives `C<=G_B=P`. This proof needs neither a general residual
formalization nor a separate mixed-witness lifting theorem.

### Explicit prospective raw formula and weaker algebraic hypotheses

The abstract pivot need not even be added as a vertex in the algebraic module.
On ambient admissible supports define

    Bpros(U) = n - max(rho(N(U)), 1+rho(N(U union {j})))  if U subset X,
    Bpros(U) = n - rho(N(U))                            otherwise.

The common-neighbour pool `N(U union {j})` is defined for every finite set;
this is not an evaluation of an age outside its support domain. In particular
the formula remains legitimate when `|U|=n` and `j notin U`.

It suffices to assume that `R` is a genuine relative age on `E`, that
`R(U)<=Bpros(U)` for every survivor support, and that the old raw singleton
bound at `j` is at least one. Positive old **canonical** singleton age implies
this last condition. The cap `R(U)<=n-1` on `X` follows because the displayed
maximum is at least one. For a nonempty positive `A`, positivity of `R(A)`
and its inequality against the truncated subtraction imply

    1 + rho(N(A union {j})) + R(A) <= n.

Thus the same pool inclusion proves `C<=B` without any global freeness
hypothesis in this purely numerical-capacity implication. Freeness of the
old graph is restored when interpreting `Bpros` as a legal one-point event;
the old singleton bound then certifies legality of that abstract pivot.

The raw formula follows from the exact clique-capacity insertion identity:
the new common-neighbour pool either omits the pivot, or contains it and
has capacity equal to the maximum of the old pool capacity and one plus
the old pool capacity linked to its full type. One may take `R` to be the
prospective canonical age restricted to `E`, with positivity on every
computed survivor support checked separately. The result derives `C<=B` and then
`C<=G_B` by the greatest-age property; it does not assume a pointed-budget
criterion or reverse the general inequality `G_B<=B`.

Nothing here chooses a numerical `v`. The finite abstract event determines
its own prospective `R`; after normalization to `C(R,X)`, a later numerical
pivot with the resulting complete column can be selected. The verified
controlled-coding theorem then retains exactly that `R`. Establishing this
chronological physical construction is the separate late-pivot task.

This prospective statement is stronger and safer than “pick an arbitrary
desired R below the survivor restriction of P”: that weaker condition does
not establish the pointed inequalities in Section 4.

## 6. Independent audit of direct finite normalization

The separate note
`docs/track_b_finite_normalization_late_pivot_english_audit_20261121.md`
proposes a finite direct normalization of any genuine target `C<=P` over
a complete actual old prefix. The construction is mathematically sound.
For each admissible support `T`, reserve an isolated clique block of size

    r_T = n - C(T),

and put column one on that whole block precisely for sorts in `T`. Every
new block is nonadjacent to every earlier original outside its own block;
every enumeration gap receives the zero active column. Old columns remain
unchanged. Blocks with `r_T=0` may be skipped.

For a nonempty test support `U`, a new block contributes all `r_T` vertices
to its common-neighbour pool when `U subset T`, and contributes none
otherwise. No common-neighbour clique can mix blocks, or mix an old
original with a block. Zero-column gaps do not enter this pool at all.
Consequently

    Bnew(U) = min(Bold(U), min_{T containing U} C(T)) = C(U).

The equality uses `Bold>=P>=C`, monotonicity of `C`, and the term `T=U`.
Zero-size blocks can be included formally in the minimum; they impose only
the universal upper bound `n`. There is no truncated-subtraction loss because
`1<=C(T)<=n`, so `n-r_T=C(T)`. The actual new canonical age is therefore
exactly `C`, and the pivot sort remains symbolic throughout.

This establishes finite target normalization, not the manuscript's exact
saturated-cover schedule. An individual support block can cause a larger
canonical drop or insert extra selected-front events. The construction also
does not compare full dependent `Kpt` sources or certify that auxiliary
parameter levels are uninteresting. These distinctions must remain explicit.

## 7. Adversarial checks and rejected strengthenings

1. **Empty survivor front.** If `E=empty`, the relative age assumptions are
   vacuous, `X=empty`, and `D={j}`. The constructor gives `C({j})=1` with
   witness `delta_j`. The prospective lower-bound proof uses only legality
   of the pivot. No nonexistent survivor witness is requested.

2. **Empty positive support.** In every formula its value is zero and its
   witness is the zero vector. The pointed contribution is exactly one.
   The proof never calls a nonempty-support theorem at the empty set.

3. **ell=2.** The constructor and prospective inequality remain valid.
   Positivity and the positive cap force `X=empty`; all admissible values
   are one. The pair-based definition of the passing set is outside its
   domain at `ell=2`, so the complete manuscript controlled-pair assertion
   is stated for `ell>=3`, as assumed in the manuscript. Direct finite
   normalization uses no blocks when `ell=2`.

4. **Zero post-age sorts.** A legal pivot can kill a positive survivor sort.
   For `ell=3`, take one protected original `a` and old columns
   `c(a,j)=c(a,x)=1`. Add `nu` adjacent to `a` and give `x` a positive bit
   at `nu`. The old age is positive but a new `x` vertex would form a
   triangle; the post-age singleton is zero. Such a sort must be discarded
   or the positivity assumption must be retained. With zero values allowed,
   the formula also need not recover `X` from pair equalities.

5. **Survivor domination is insufficient.** Still with `ell=3`, let `P`
   be the constant-one age on `{j,x}`, let `R({x})=1`, and take `X={x}`.
   Then `R<=P` on survivors and the positive cap holds, but
   `C({j,x})=2>P({j,x})=1`. This is exactly the obstruction in item 4 if
   one incorrectly substitutes a desired positive `R` for the actual
   prospective post-age.

6. **The all-support cap cannot be replaced by proper-support caps.** For
   `ell=4`, let `E=X` have three sorts and let `R(U)=|U|`. Every positive
   support of size less than three has value at most two, but `R(E)=3`.
   The displayed constructor is still a genuine age, yet it violates the
   controlled cap on `E`, and coding the pivot forbids the three-vertex
   positive clique. Thus the post-age is not `R`. The proof of exact coding
   genuinely uses the size-`n` cap on the positive-weight support.

7. **Singleton caps alone are insufficient.** For `ell=4`, take two
   survivor sorts with singleton ages two and pair age three, and make
   both positive. These values form a genuine age. The constructor on the
   three-sort support containing `j` would have value four, above `n=3`.

8. **Complete pointed data are necessary.** Equality of the age on
   survivor sorts alone does not determine the residual after a positive
   pivot. The old pivot reference column records how its neighbours overlap
   with survivor common-neighbour pools. The earlier residual audit gives
   an explicit `K_4` example. Omitting a committed parameter original can
   similarly conceal a mixed forbidden clique.

9. **A numerical pivot already chosen cannot be delayed.** Newly reserved
   numerical originals cannot be inserted before its fixed index. A block
   isolated from all committed originals is also isolated from such a
   fixed pivot, which may conflict with the required positive pivot column.
   The prospective construction applies to the next uncommitted original.

10. **Raw and canonical ages are not interchanged silently.** The
    prospective proof transfers complete normalized vectors by the verified
    raw/canonical equivalence. It does not assume `B=P`. Direct all-support
    normalization is stronger: it explicitly makes the final raw bound
    equal to `C`, and only then concludes its canonical age is `C`.

11. **No mixed-block loophole in direct normalization.** Each new block is
    isolated from the full earlier prefix, not merely from other designated
    blocks. This is what rules out cliques using an old parameter and a
    new block. Assigning zero columns only to a subset of intervening
    originals would not give the stated raw formula.

12. **No empty active-domain obstruction.** The direct normalization theorem
    with `d=0` has no supports and needs no blocks. The pre-age constructor
    itself has a distinguished `j`, so its domain is necessarily nonempty.
    Numerical-stage APIs requiring a positive number of future sorts may
    need a separate vacuous branch, rather than a false nonemptiness proof.

13. **Finite normalization does not settle history.** Exact final ordinary
    age and a legal late pivot do not classify earlier interesting cuts,
    compare dependent upper types or auxiliary `E` records, prove the
    corrected-(B3) source equivalence, or construct a common labelled
    inverse source. No global validation colour follows from this note.

## 8. Implemented formalization and remaining scope

`Kk/ControlledPreAge.lean` implements the genuine constructor, pivot singleton,
survivor restriction, positive cap and growth, passing-set recovery on
admissible pairs, final controlled maximum identity, uniqueness, and the exact
lower-bound criterion of Section 4. Its canonical-positivity helper constructs
the relative consistency witnesses, so a computed canonical post-age does not
need a separate assumed age-consistency hypothesis.

`Kk/ProspectiveControlledPreAge.lean` defines the literal prospective raw
formula, proves its equality to the abstract one-point graph's raw bound,
derives legality from the old positive pivot singleton, and proves the cap
and `C(R,X) <= B_old`, hence `C(R,X) <= P`. The final prospective theorem
defines `R` by canonicalization and assumes only positivity on every computed
survivor support and at the old pivot singleton. It uses the direct capacity
proof in Section 5, without assuming the desired pointed inequalities or
formalizing the general residual-vector operation.

`Kk/PhysicalProspectiveControlledCoding.lean` then consumes this computed target,
constructs the complete actual raw equality through finitely many isolated
support cliques, and selects the actual pivot afterwards. Its post-age is
exactly `R(pi[U])`; a second endpoint supplies one complete finite numerical
Henson stage fixing the entire prefix through the same pivot. Arbitrary parent
maps are allowed, provided every parent is a survivor and every positive
child has its parent in `X`. All already committed originals must be in the
initial protected prefix. These modules passed the complete hosted gate
recorded above; the exact new endpoint list is in
[`scripts/check_track_b_controlled_preage.lean`](../scripts/check_track_b_controlled_preage.lean).

Their finite conclusion does not settle a prescribed saturated-cover order or
the full dependent chronological history. The remaining Kpt/auxiliary E,
(I1)–(I3)/corrected-(B3), common-orbit and infinite-diary obligations remain
separate.
